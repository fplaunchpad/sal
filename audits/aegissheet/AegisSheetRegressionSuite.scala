package ex2025tabular

import munit.FunSuite
import rdts.base.{LocalUid, Uid}
import webapps.ex2025tabular.lib.*
import webapps.ex2025tabular.lib.Spreadsheet.{Range, SpreadsheetCoordinate}

/** Paper-derived regressions for Bismuth commit dd4c614.
  *
  * Run this file as an additional exWeb test source. The three `bug` tests and
  * the range-crossing test fail at dd4c614. The two controls pass.
  */
final class AegisSheetRegressionSuite extends FunSuite:

  private def sheetWithRows(count: Int): Spreadsheet[String] =
    SpreadsheetDeltaAggregator(Spreadsheet[String](), LocalUid.predefined("audit-setup"))
      .repeatEdit(count, _.addRow().delta, allowUndo = false)
      .edit(_.addColumn().delta, allowUndo = false)
      .current

  test("bug: Table 4 move undo preserves a concurrent insert") {
    val initial = sheetWithRows(3)
    val original = initial.listRowIds
    val mover = SpreadsheetDeltaAggregator(initial, LocalUid.predefined("audit-mover"))
    val inserter = SpreadsheetDeltaAggregator(initial, LocalUid.predefined("audit-inserter"))

    val move = mover.editAndGetDelta()(_.moveRow(0.toRowIndex, 3.toRowIndex))
    val insert = inserter.editAndGetDelta()(_.insertRow(1.toRowIndex).delta)
    val inserted = inserter.current.listRowIds.find(id => !original.contains(id)).get
    mover.accumulate(insert)
    inserter.accumulate(move)

    val undo = mover.undoAndGetDelta().get
    inserter.accumulate(undo)

    val expected = List(original(0), inserted, original(1), original(2))
    assertEquals(mover.current.listRowIds, expected)
    assertEquals(inserter.current.listRowIds, expected)
  }

  test("bug: Table 4 move undo reverts both concurrent moves") {
    val initial = sheetWithRows(4)
    val moverA = SpreadsheetDeltaAggregator(initial, LocalUid.predefined("audit-move-a"))
    val moverB = SpreadsheetDeltaAggregator(initial, LocalUid.predefined("audit-move-b"))

    val moveA = moverA.editAndGetDelta()(_.moveRow(0.toRowIndex, 4.toRowIndex))
    val moveB = moverB.editAndGetDelta()(_.moveRow(0.toRowIndex, 2.toRowIndex))
    moverA.accumulate(moveB)
    moverB.accumulate(moveA)

    val undo = moverA.undoAndGetDelta().get
    moverB.accumulate(undo)

    assertEquals(moverA.current.listRowIds, initial.listRowIds)
    assertEquals(moverB.current.listRowIds, initial.listRowIds)
  }

  test("control: Table 4 move undo reverts a concurrent remove") {
    val initial = sheetWithRows(3)
    val mover = SpreadsheetDeltaAggregator(initial, LocalUid.predefined("audit-remove-mover"))
    val remover = SpreadsheetDeltaAggregator(initial, LocalUid.predefined("audit-remover"))

    val move = mover.editAndGetDelta()(_.moveRow(0.toRowIndex, 3.toRowIndex))
    val remove = remover.editAndGetDelta()(_.removeRow(0.toRowIndex))
    mover.accumulate(remove)
    remover.accumulate(move)

    val undo = mover.undoAndGetDelta().get
    remover.accumulate(undo)

    assertEquals(mover.current.listRowIds, initial.listRowIds)
    assertEquals(remover.current.listRowIds, initial.listRowIds)
  }

  test("bug: range undo preserves stable endpoints after concurrent insert") {
    val id = RangeId(Uid("audit-range"))
    val range = Range(
      SpreadsheetCoordinate(1.toRowIndex, 0.toColumnIndex),
      SpreadsheetCoordinate(2.toRowIndex, 0.toColumnIndex)
    )
    val initial = SpreadsheetDeltaAggregator(sheetWithRows(4), LocalUid.predefined("audit-range-setup"))
      .edit(_.addRange(id, range.from, range.to), allowUndo = false)
      .current
    val remover = SpreadsheetDeltaAggregator(initial, LocalUid.predefined("audit-range-remover"))
    val inserter = SpreadsheetDeltaAggregator(initial, LocalUid.predefined("audit-range-inserter"))

    val remove = remover.editAndGetDelta()(_.removeRange(id))
    val insert = inserter.editAndGetDelta()(_.insertRow(0.toRowIndex).delta)
    remover.accumulate(insert)
    inserter.accumulate(remove)

    val undo = remover.undoAndGetDelta().get
    inserter.accumulate(undo)

    val expected = Some(Range(
      SpreadsheetCoordinate(2.toRowIndex, 0.toColumnIndex),
      SpreadsheetCoordinate(3.toRowIndex, 0.toColumnIndex)
    ))
    assertEquals(remover.current.getRange(id), expected)
    assertEquals(inserter.current.getRange(id), expected)
  }

  test("bug: crossing a range discards it without crashing listRanges") {
    val id = RangeId(Uid("audit-crossed-range"))
    val range = Range(
      SpreadsheetCoordinate(1.toRowIndex, 1.toColumnIndex),
      SpreadsheetCoordinate(3.toRowIndex, 3.toColumnIndex)
    )
    val initial = SpreadsheetDeltaAggregator(Spreadsheet[String](), LocalUid.predefined("audit-cross-setup"))
      .repeatEdit(5, _.addRow().delta, allowUndo = false)
      .repeatEdit(5, _.addColumn().delta, allowUndo = false)
      .edit(_.addRange(id, range.from, range.to), allowUndo = false)
      .current
    val replica = SpreadsheetDeltaAggregator(initial, LocalUid.predefined("audit-cross-mover"))

    replica.edit(_.moveColumn(3.toColumnIndex, 1.toColumnIndex), allowUndo = false)

    assertEquals(replica.current.getRange(id), None)
    assertEquals(replica.current.listRanges(), List.empty)
  }

  test("control: purge keeps a concurrent unseen edit") {
    val coordinate = SpreadsheetCoordinate(0.toRowIndex, 0.toColumnIndex)
    val initial = SpreadsheetDeltaAggregator(sheetWithRows(1), LocalUid.predefined("audit-cell-setup"))
      .edit(_.editCell(coordinate, Some("old")), allowUndo = false)
      .current
    val collector = SpreadsheetDeltaAggregator(initial, LocalUid.predefined("audit-collector"))
    val editor = SpreadsheetDeltaAggregator(initial, LocalUid.predefined("audit-editor"))

    val purge = collector.multiEditAndGetDelta()(
      _.removeRow(0.toRowIndex),
      _.purgeTombstones
    )
    val edit = editor.editAndGetDelta()(_.editCell(coordinate, Some("new")))
    collector.accumulate(edit)
    editor.accumulate(purge)

    assertEquals(collector.current.read(coordinate).toList, List("new"))
    assertEquals(editor.current.read(coordinate).toList, List("new"))
  }
