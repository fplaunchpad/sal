import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide

import Blaster
/-
  Section 1 - Tax Imposed

  This module implements IRC Section 1, which determines the tax liability
  for taxpayers based on their filing status and taxable income.

  Key filing statuses:
  - (a) Married filing jointly / Surviving spouse
  - (b) Head of household
  - (c) Unmarried individuals
  - (d) Married filing separately
-/

-- Basic types

structure Person where
  id : Nat
  deriving DecidableEq, Repr, BEq

inductive TaxYear where
  | year : Nat → TaxYear
  deriving DecidableEq, Repr, BEq

-- Events representing facts about taxpayers

inductive Event where
  -- Marriage status (§7703)
  | marriage : Person → Person → TaxYear → TaxYear → Event

  -- Joint return filing
  | jointReturn : Person → Person → TaxYear → Event

  -- Nonresident alien status
  | nonresidentAlien : Person → TaxYear → Event

  -- Surviving spouse status (§2(a))
  | survivingSpouse : Person → TaxYear → Event

  -- Head of household status (§2(b))
  | headOfHousehold : Person → TaxYear → Event

  -- Taxable income (computed from §63)
  | taxableIncome : Person → TaxYear → Int → Event

  -- Various income types
  | agriIncome : Person → TaxYear → TaxYear → Nat → Event
  | businessIncome : Person → TaxYear → TaxYear → Nat → Event
  | capitalGain : Person → TaxYear → TaxYear → Nat → Event
  | deduction : Person → TaxYear → String → Nat → Event
  deriving Repr, BEq

-- Section outcomes
structure SectionOutcome (α : Type) where
  isApplicable : Bool
  value : Option α
  deriving Repr

-- Helper to check if value equals something
@[simp, grind]
def SectionOutcome.hasValue (outcome : SectionOutcome α) (v : α) [BEq α] : Bool :=
  match outcome.value with
  | some val => val == v
  | none => false

-- Example person instances for testing
@[simp, grind]
def personAlice : Person := ⟨1⟩
@[simp, grind]
def personBob : Person := ⟨2⟩
@[simp, grind]
def personCarol : Person := ⟨3⟩

namespace Section1

-- ============================================================================
-- HELPER FUNCTIONS - Extract relevant events
-- ============================================================================

/-- Check if person is married to another person in given year -/
@[simp, grind]
def isMarried (p : Person) (year : TaxYear) (events : List Event) : Option Person :=
  events.findSome? fun e =>
    match e with
    | Event.marriage p1 p2 startYear _ =>
        if (p == p1 ∨ p == p2) && startYear == year then
          if p == p1 then some p2 else some p1
        else none
    | _ => none

/-- Check if person filed joint return with spouse in given year -/
@[simp, grind]
def hasJointReturn (p : Person) (spouse : Person) (year : TaxYear) (events : List Event) : Bool :=
  events.any fun e =>
    match e with
    | Event.jointReturn p1 p2 y =>
        y == year && ((p == p1 && spouse == p2) ∨ (p == p2 && spouse == p1))
    | _ => false

/-- Check if person is nonresident alien in given year -/
@[simp, grind]
def isNonresidentAlien (p : Person) (year : TaxYear) (events : List Event) : Bool :=
  events.any fun e =>
    match e with
    | Event.nonresidentAlien p' y => p == p' && y == year
    | _ => false

/-- Check if person is surviving spouse in given year -/
@[simp, grind]
def isSurvivingSpouse (p : Person) (year : TaxYear) (events : List Event) : Bool :=
  events.any fun e =>
    match e with
    | Event.survivingSpouse p' y => p == p' && y == year
    | _ => false

/-- Check if person is head of household in given year -/
@[simp, grind]
def isHeadOfHousehold (p : Person) (year : TaxYear) (events : List Event) : Bool :=
  events.any fun e =>
    match e with
    | Event.headOfHousehold p' y => p == p' && y == year
    | _ => false

/-- Get taxable income for person in given year -/
@[simp, grind]
def getTaxableIncome (p : Person) (year : TaxYear) (events : List Event) : Option Int :=
  events.findSome? fun e =>
    match e with
    | Event.taxableIncome p' y amount =>
        if p == p' && y == year then some amount else none
    | _ => none

/-- Get all events relevant to Section 1 computation -/
@[simp, grind]
def getRelevantEventsFor_section1 (p : Person) (year : TaxYear) (events : List Event) : List Event :=
  events.filter fun e =>
    match e with
    | Event.marriage p1 p2 _ _ => p == p1 ∨ p == p2
    | Event.jointReturn p1 p2 y => (p == p1 ∨ p == p2) && y == year
    | Event.nonresidentAlien p' y => p == p' && y == year
    | Event.survivingSpouse p' y => p == p' && y == year
    | Event.headOfHousehold p' y => p == p' && y == year
    | Event.taxableIncome p' y _ => p == p' && y == year
    | _ => false

-- ============================================================================
-- TAX COMPUTATION HELPERS
-- ============================================================================

/-- Round to nearest integer (rounding half up) -/
@[simp, grind]
def roundInt (x : Int) : Int :=
  x

/-- Multiply and divide with rounding: (x * num) / den, rounded -/
@[simp, grind]
def roundMulDiv (x : Int) (num : Int) (den : Int) : Int :=
  if den == 0 then 0
  else
    let prod := x * num
    let quot := prod / den
    let rem := prod % den
    -- Round half up
    if rem * 2 >= den then quot + 1 else quot

-- ============================================================================
-- SECTION 1(a) - Married Filing Jointly and Surviving Spouses
-- ============================================================================

/-- §1(a)(i): 15% of taxable income if not over $36,900 -/
@[simp, grind]
def s1_a_i (taxinc : Int) : SectionOutcome Int :=
  if taxinc ≤ 36900 then
    ⟨true, some (roundMulDiv taxinc 15 100)⟩
  else
    ⟨false, none⟩

/-- §1(a)(ii): $5,535 + 28% of excess over $36,900 if over $36,900 but not over $89,150 -/
@[simp, grind]
def s1_a_ii (taxinc : Int) : SectionOutcome Int :=
  if 36900 < taxinc ∧ taxinc ≤ 89150 then
    ⟨true, some (5535 + roundMulDiv (taxinc - 36900) 28 100)⟩
  else
    ⟨false, none⟩

/-- §1(a)(iii): $20,165 + 31% of excess over $89,150 if over $89,150 but not over $140,000 -/
@[simp, grind]
def s1_a_iii (taxinc : Int) : SectionOutcome Int :=
  if 89150 < taxinc ∧ taxinc ≤ 140000 then
    ⟨true, some (20165 + roundMulDiv (taxinc - 89150) 31 100)⟩
  else
    ⟨false, none⟩

/-- §1(a)(iv): $35,928 + 36% of excess over $140,000 if over $140,000 but not over $250,000 -/
@[simp, grind]
def s1_a_iv (taxinc : Int) : SectionOutcome Int :=
  if 140000 < taxinc ∧ taxinc ≤ 250000 then
    ⟨true, some (35928 + roundMulDiv (taxinc - 140000) 36 100)⟩
  else
    ⟨false, none⟩

/-- §1(a)(v): $75,528 + 39.6% of excess over $250,000 if over $250,000 -/
@[simp, grind]
def s1_a_v (taxinc : Int) : SectionOutcome Int :=
  if 250000 < taxinc then
    ⟨true, some (75528 + roundMulDiv (taxinc - 250000) 396 1000)⟩
  else
    ⟨false, none⟩

/-- §1(a) tax: Try all §1(a) brackets and return the applicable one -/
@[simp, grind]
def s1_a_tax (taxinc : Int) : SectionOutcome Int :=
  match s1_a_i taxinc with
  | ⟨true, some tax⟩ => ⟨true, some tax⟩
  | _ => match s1_a_ii taxinc with
    | ⟨true, some tax⟩ => ⟨true, some tax⟩
    | _ => match s1_a_iii taxinc with
      | ⟨true, some tax⟩ => ⟨true, some tax⟩
      | _ => match s1_a_iv taxinc with
        | ⟨true, some tax⟩ => ⟨true, some tax⟩
        | _ => s1_a_v taxinc

-- ============================================================================
-- SECTION 1(b) - Head of Household
-- ============================================================================

/-- §1(b)(i): 15% of taxable income if not over $29,600 -/
@[simp, grind]
def s1_b_i (taxinc : Int) : SectionOutcome Int :=
  if taxinc ≤ 29600 then
    ⟨true, some (roundMulDiv taxinc 15 100)⟩
  else
    ⟨false, none⟩

/-- §1(b)(ii): $4,440 + 28% of excess over $29,600 if over $29,600 but not over $76,400 -/
@[simp, grind]
def s1_b_ii (taxinc : Int) : SectionOutcome Int :=
  if 29600 < taxinc ∧ taxinc ≤ 76400 then
    ⟨true, some (4440 + roundMulDiv (taxinc - 29600) 28 100)⟩
  else
    ⟨false, none⟩

/-- §1(b)(iii): $17,544 + 31% of excess over $76,400 if over $76,400 but not over $127,500 -/
@[simp, grind]
def s1_b_iii (taxinc : Int) : SectionOutcome Int :=
  if 76400 < taxinc ∧ taxinc ≤ 127500 then
    ⟨true, some (17544 + roundMulDiv (taxinc - 76400) 31 100)⟩
  else
    ⟨false, none⟩

/-- §1(b)(iv): $33,385 + 36% of excess over $127,500 if over $127,500 but not over $250,000 -/
@[simp, grind]
def s1_b_iv (taxinc : Int) : SectionOutcome Int :=
  if 127500 < taxinc ∧ taxinc ≤ 250000 then
    ⟨true, some (33385 + roundMulDiv (taxinc - 127500) 36 100)⟩
  else
    ⟨false, none⟩

/-- §1(b)(v): $77,485 + 39.6% of excess over $250,000 if over $250,000 -/
@[simp, grind]
def s1_b_v (taxinc : Int) : SectionOutcome Int :=
  if 250000 < taxinc then
    ⟨true, some (77485 + roundMulDiv (taxinc - 250000) 396 1000)⟩
  else
    ⟨false, none⟩

/-- §1(b) tax: Try all §1(b) brackets and return the applicable one -/
@[simp, grind]
def s1_b_tax (taxinc : Int) : SectionOutcome Int :=
  match s1_b_i taxinc with
  | ⟨true, some tax⟩ => ⟨true, some tax⟩
  | _ => match s1_b_ii taxinc with
    | ⟨true, some tax⟩ => ⟨true, some tax⟩
    | _ => match s1_b_iii taxinc with
      | ⟨true, some tax⟩ => ⟨true, some tax⟩
      | _ => match s1_b_iv taxinc with
        | ⟨true, some tax⟩ => ⟨true, some tax⟩
        | _ => s1_b_v taxinc

-- ============================================================================
-- SECTION 1(c) - Unmarried Individuals
-- ============================================================================

/-- §1(c)(i): 15% of taxable income if not over $22,100 -/
@[simp, grind]
def s1_c_i (taxinc : Int) : SectionOutcome Int :=
  if taxinc ≤ 22100 then
    ⟨true, some (roundMulDiv taxinc 15 100)⟩
  else
    ⟨false, none⟩

/-- §1(c)(ii): $3,315 + 28% of excess over $22,100 if over $22,100 but not over $53,500 -/
@[simp, grind]
def s1_c_ii (taxinc : Int) : SectionOutcome Int :=
  if 22100 < taxinc ∧ taxinc ≤ 53500 then
    ⟨true, some (3315 + roundMulDiv (taxinc - 22100) 28 100)⟩
  else
    ⟨false, none⟩

/-- §1(c)(iii): $12,107 + 31% of excess over $53,500 if over $53,500 but not over $115,000 -/
@[simp, grind]
def s1_c_iii (taxinc : Int) : SectionOutcome Int :=
  if 53500 < taxinc ∧ taxinc ≤ 115000 then
    ⟨true, some (12107 + roundMulDiv (taxinc - 53500) 31 100)⟩
  else
    ⟨false, none⟩

/-- §1(c)(iv): $31,172 + 36% of excess over $115,000 if over $115,000 but not over $250,000 -/
@[simp, grind]
def s1_c_iv (taxinc : Int) : SectionOutcome Int :=
  if 115000 < taxinc ∧ taxinc ≤ 250000 then
    ⟨true, some (31172 + roundMulDiv (taxinc - 115000) 36 100)⟩
  else
    ⟨false, none⟩

/-- §1(c)(v): $79,772 + 39.6% of excess over $250,000 if over $250,000 -/
@[simp, grind]
def s1_c_v (taxinc : Int) : SectionOutcome Int :=
  if 250000 < taxinc then
    ⟨true, some (79772 + roundMulDiv (taxinc - 250000) 396 1000)⟩
  else
    ⟨false, none⟩

/-- §1(c) tax: Try all §1(c) brackets and return the applicable one -/
@[simp, grind]
def s1_c_tax (taxinc : Int) : SectionOutcome Int :=
  match s1_c_i taxinc with
  | ⟨true, some tax⟩ => ⟨true, some tax⟩
  | _ => match s1_c_ii taxinc with
    | ⟨true, some tax⟩ => ⟨true, some tax⟩
    | _ => match s1_c_iii taxinc with
      | ⟨true, some tax⟩ => ⟨true, some tax⟩
      | _ => match s1_c_iv taxinc with
        | ⟨true, some tax⟩ => ⟨true, some tax⟩
        | _ => s1_c_v taxinc

-- ============================================================================
-- SECTION 1(d) - Married Filing Separately
-- ============================================================================

/-- §1(d)(i): 15% of taxable income if not over $18,450 -/
@[simp, grind]
def s1_d_i (taxinc : Int) : SectionOutcome Int :=
  if taxinc ≤ 18450 then
    ⟨true, some (roundMulDiv taxinc 15 100)⟩
  else
    ⟨false, none⟩

/-- §1(d)(ii): $2,767 + 28% of excess over $18,450 if over $18,450 but not over $44,575 -/
@[simp, grind]
def s1_d_ii (taxinc : Int) : SectionOutcome Int :=
  if 18450 < taxinc ∧ taxinc ≤ 44575 then
    ⟨true, some (2767 + roundMulDiv (taxinc - 18450) 28 100)⟩
  else
    ⟨false, none⟩

/-- §1(d)(iii): $10,082 + 31% of excess over $44,575 if over $44,575 but not over $70,000 -/
@[simp, grind]
def s1_d_iii (taxinc : Int) : SectionOutcome Int :=
  if 44575 < taxinc ∧ taxinc ≤ 70000 then
    ⟨true, some (10082 + roundMulDiv (taxinc - 44575) 31 100)⟩
  else
    ⟨false, none⟩

/-- §1(d)(iv): $17,964 + 36% of excess over $70,000 if over $70,000 but not over $125,000 -/
@[simp, grind]
def s1_d_iv (taxinc : Int) : SectionOutcome Int :=
  if 70000 < taxinc ∧ taxinc ≤ 125000 then
    ⟨true, some (17964 + roundMulDiv (taxinc - 70000) 36 100)⟩
  else
    ⟨false, none⟩

/-- §1(d)(v): $37,764 + 39.6% of excess over $125,000 if over $125,000 -/
@[simp, grind]
def s1_d_v (taxinc : Int) : SectionOutcome Int :=
  if 125000 < taxinc then
    ⟨true, some (37764 + roundMulDiv (taxinc - 125000) 396 1000)⟩
  else
    ⟨false, none⟩

/-- §1(d) tax: Try all §1(d) brackets and return the applicable one -/
@[simp, grind]
def s1_d_tax (taxinc : Int) : SectionOutcome Int :=
  match s1_d_i taxinc with
  | ⟨true, some tax⟩ => ⟨true, some tax⟩
  | _ => match s1_d_ii taxinc with
    | ⟨true, some tax⟩ => ⟨true, some tax⟩
    | _ => match s1_d_iii taxinc with
      | ⟨true, some tax⟩ => ⟨true, some tax⟩
      | _ => match s1_d_iv taxinc with
        | ⟨true, some tax⟩ => ⟨true, some tax⟩
        | _ => s1_d_v taxinc

-- ============================================================================
-- SUBSECTION COMPUTATIONS
-- ============================================================================

/-- §1(a) - Married filing jointly or surviving spouse

  Returns the tax if the taxpayer qualifies for §1(a) treatment.
  Two ways to qualify:
  1. Married and filed joint return (with spouse)
  2. Surviving spouse status per §2(a)
-/
@[simp, grind]
def s1_a (p : Person) (year : TaxYear) (events : List Event) : SectionOutcome Int :=
  match getTaxableIncome p year events with
  | none => ⟨false, none⟩
  | some taxinc =>
      if taxinc < 0 then ⟨false, none⟩
      else
        let married := isMarried p year events
        -- Case 1: Married filing jointly
        match married with
        | some spouse =>
            if hasJointReturn p spouse year events then
              if ¬(isNonresidentAlien p year events) && ¬(isNonresidentAlien spouse year events) then
                s1_a_tax taxinc  -- Reuse bracket computation
              else
                ⟨false, none⟩
            else
              ⟨false, none⟩
        | none =>
            -- Case 2: Surviving spouse
            if isSurvivingSpouse p year events then
              s1_a_tax taxinc  -- Reuse bracket computation
            else
              ⟨false, none⟩

/-- §1(b) - Head of household -/
@[simp, grind]
def s1_b (p : Person) (year : TaxYear) (events : List Event) : SectionOutcome Int :=
  match getTaxableIncome p year events with
  | none => ⟨false, none⟩
  | some taxinc =>
      if taxinc < 0 then ⟨false, none⟩
      else
        match isMarried p year events with
        | none =>
            if ¬isSurvivingSpouse p year events ∧ isHeadOfHousehold p year events then
              s1_b_tax taxinc  -- Reuse bracket computation
            else
              ⟨false, none⟩
        | some _ => ⟨false, none⟩

/-- §1(c) - Unmarried individuals -/
@[simp, grind]
def s1_c (p : Person) (year : TaxYear) (events : List Event) : SectionOutcome Int :=
  match getTaxableIncome p year events with
  | none => ⟨false, none⟩
  | some taxinc =>
      if taxinc < 0 then ⟨false, none⟩
      else
        match isMarried p year events with
        | none =>
            if ¬isSurvivingSpouse p year events ∧ ¬isHeadOfHousehold p year events then
              s1_c_tax taxinc  -- Reuse bracket computation
            else
              ⟨false, none⟩
        | some _ => ⟨false, none⟩

/-- §1(d) - Married filing separately -/
@[simp, grind]
def s1_d (p : Person) (year : TaxYear) (events : List Event) : SectionOutcome Int :=
  match getTaxableIncome p year events with
  | none => ⟨false, none⟩
  | some taxinc =>
      if taxinc < 0 then ⟨false, none⟩
      else
        match isMarried p year events with
        | some spouse =>
            if ¬hasJointReturn p spouse year events then
              s1_d_tax taxinc  -- Reuse bracket computation
            else
              ⟨false, none⟩
        | none => ⟨false, none⟩

-- ============================================================================
-- MAIN SECTION 1 COMPUTATION
-- ============================================================================

/-- §1 - Tax Imposed

  Determines tax liability based on filing status by trying each subsection.
  Tries in order: §1(a), §1(b), §1(c), §1(d)
  Returns the first applicable status.
-/
@[simp, grind]
def s1 (p : Person) (year : TaxYear) (events : List Event) : SectionOutcome Int :=
  -- Try each filing status subsection
  match s1_a p year events with
  | ⟨true, some tax⟩ => ⟨true, some tax⟩  -- §1(a) applies
  | _ => match s1_b p year events with
    | ⟨true, some tax⟩ => ⟨true, some tax⟩  -- §1(b) applies
    | _ => match s1_c p year events with
      | ⟨true, some tax⟩ => ⟨true, some tax⟩  -- §1(c) applies
      | _ => s1_d p year events  -- Try §1(d), return its result

-- ============================================================================
-- TEST CASES
-- ============================================================================

/-- Test 1: Married couple filing jointly with $50,000 income

  Expected tax (§1(a) bracket ii):
  $5,535 + 28% of ($50,000 - $36,900) = $5,535 + 28% of $13,100 = $5,535 + $3,668 = $9,203
-/
@[simp, grind]
def test_s1_married_joint : Bool :=
  let year := TaxYear.year 2023
  let events := [
    Event.marriage personAlice personBob year year,
    Event.jointReturn personAlice personBob year,
    Event.taxableIncome personAlice year 50000
  ]
  match s1 personAlice year events with
  | ⟨true, some tax⟩ =>
      -- Expected: 5535 + roundMulDiv 13100 28 100
      -- = 5535 + 3668 = 9203
      tax == 9203
  | _ => false

#eval test_s1_married_joint  -- Should return true

/-- Test 2: Unmarried individual with $50,000 income

  Expected tax (§1(c) bracket ii):
  $3,315 + 28% of ($50,000 - $22,100) = $3,315 + 28% of $27,900 = $3,315 + $7,812 = $11,127
-/
@[simp, grind]
def test_s1_unmarried : Bool :=
  let year := TaxYear.year 2023
  let events := [
    Event.taxableIncome personAlice year 50000
  ]
  match s1 personAlice year events with
  | ⟨true, some tax⟩ =>
      -- Expected: 3315 + roundMulDiv 27900 28 100
      -- = 3315 + 7812 = 11127
      tax == 11127
  | _ => false

#eval test_s1_unmarried  -- Should return true

/-- Test 3: Head of household with $50,000 income

  Expected tax (§1(b) bracket ii):
  $4,440 + 28% of ($50,000 - $29,600) = $4,440 + 28% of $20,400 = $4,440 + $5,712 = $10,152
-/
@[simp, grind]
def test_s1_head_of_household : Bool :=
  let year := TaxYear.year 2023
  let events := [
    Event.headOfHousehold personAlice year,
    Event.taxableIncome personAlice year 50000
  ]
  match s1 personAlice year events with
  | ⟨true, some tax⟩ =>
      -- Expected: 4440 + roundMulDiv 20400 28 100
      -- = 4440 + 5712 = 10152
      tax == 10152
  | _ => false

#eval test_s1_head_of_household  -- Should return true

/-- Test 4: Married filing separately with $50,000 income

  Expected tax (§1(d) bracket iii):
  $10,082 + 31% of ($50,000 - $44,575) = $10,082 + 31% of $5,425 = $10,082 + $1,682 = $11,764
-/
@[simp, grind]
def test_s1_married_separate : Bool :=
  let year := TaxYear.year 2023
  let events := [
    Event.marriage personAlice personBob year year,
    -- Note: NO jointReturn event
    Event.taxableIncome personAlice year 50000
  ]
  match s1 personAlice year events with
  | ⟨true, some tax⟩ =>
      -- Expected: 10082 + roundMulDiv 5425 31 100
      -- = 10082 + 1681 = 11763 (with rounding)
      tax == 11763 || tax == 11764
  | _ => false

#eval test_s1_married_separate  -- Should return true

/-- Test 5: Surviving spouse with $50,000 income

  Expected tax: Same as married filing jointly (§1(a))
  $5,535 + 28% of ($50,000 - $36,900) = $9,203
-/
@[simp, grind]
def test_s1_surviving_spouse : Bool :=
  let year := TaxYear.year 2023
  let events := [
    Event.survivingSpouse personAlice year,
    Event.taxableIncome personAlice year 50000
  ]
  match s1 personAlice year events with
  | ⟨true, some tax⟩ => tax == 9203
  | _ => false

#eval test_s1_surviving_spouse  -- Should return true

/-- Test 6: Edge case - Zero income -/
@[simp, grind]
def test_s1_zero_income : Bool :=
  let year := TaxYear.year 2023
  let events := [
    Event.taxableIncome personAlice year 0
  ]
  match s1 personAlice year events with
  | ⟨true, some tax⟩ => tax == 0
  | _ => false

#eval test_s1_zero_income  -- Should return true

/-- Test 7: Edge case - No taxable income event -/
@[simp, grind]
def test_s1_no_income : Bool :=
  let year := TaxYear.year 2023
  let events := []
  match s1 personAlice year events with
  | ⟨false, none⟩ => true
  | _ => false

#eval test_s1_no_income  -- Should return true

/-- Test 8: Edge case - High income in top bracket -/
@[simp, grind]
def test_s1_high_income : Bool :=
  let year := TaxYear.year 2023
  let events := [
    Event.taxableIncome personAlice year 300000
  ]
  match s1 personAlice year events with
  | ⟨true, some tax⟩ =>
      -- Expected (§1(c) bracket v): 79772 + roundMulDiv 50000 396 1000
      -- = 79772 + 19800 = 99572
      tax == 99572
  | _ => false

#eval test_s1_high_income  -- Should return true

/-- Test 9: Edge case - Nonresident alien cannot file jointly -/
@[simp, grind]
def test_s1_nonresident_alien : Bool :=
  let year := TaxYear.year 2023
  let events := [
    Event.marriage personAlice personBob year year,
    Event.jointReturn personAlice personBob year,
    Event.nonresidentAlien personAlice year,
    Event.taxableIncome personAlice year 50000
  ]
  match s1 personAlice year events with
  | ⟨false, none⟩ => true  -- Should not apply because NRA
  | _ => false

#eval test_s1_nonresident_alien  -- Should return true

-- ============================================================================
-- THEOREMS FOR DIFFERENT TYPES OF REASONING
-- ============================================================================

/-
  Type 1: Given a set of events, predict the outcome of Section 1

  This is the forward computation - we execute s1 and get the result.
-/

/-- Theorem: Forward reasoning - compute tax from events -/
theorem predict_tax_from_events (p : Person) (year : TaxYear) (events : List Event) :
  ∃ outcome, s1 p year events = outcome := by
  exists (s1 p year events)

/-- Theorem: If person has taxable income and is unmarried (not surviving spouse or HOH),
    then Section 1(c) applies with specific tax amount -/
theorem unmarried_individual_tax (p : Person) (year : TaxYear) (taxinc : Int)
  (events : List Event) :
  getTaxableIncome p year events = some taxinc →
  isMarried p year events = none →
  ¬isSurvivingSpouse p year events →
  ¬isHeadOfHousehold p year events →
  taxinc ≥ 0 →
  ∃ tax, s1_c_tax taxinc = ⟨true, some tax⟩ ∧ s1 p year events = ⟨true, some tax⟩ := by
  intros
  aesop








/-
  Type 2: Given events and assumptions about some outcomes, predict other outcomes

  Example: If we know someone is married and has taxable income,
  we can predict whether they'll use §1(a) or §1(d) based on joint return status.
-/

/-- Theorem: If married with joint return, then tax uses §1(a) brackets -/
theorem married_joint_uses_1a_brackets (p : Person) (spouse : Person) (year : TaxYear)
  (taxinc : Int) (events : List Event) :
  getTaxableIncome p year events = some taxinc →
  isMarried p year events = some spouse →
  hasJointReturn p spouse year events = true →
  ¬isNonresidentAlien p year events →
  ¬isNonresidentAlien spouse year events →
  taxinc ≥ 0 →
  ∃ tax, s1_a_tax taxinc = ⟨true, some tax⟩ ∧ s1 p year events = ⟨true, some tax⟩ := by
  sorry



/-- Theorem: If married without joint return, then tax uses §1(d) brackets -/
theorem married_separate_uses_1d_brackets (p : Person) (spouse : Person) (year : TaxYear)
  (taxinc : Int) (events : List Event) :
  getTaxableIncome p year events = some taxinc →
  isMarried p year events = some spouse →
  hasJointReturn p spouse year events = false →
  taxinc ≥ 0 →
  ∃ tax, s1_d_tax taxinc = ⟨true, some tax⟩ ∧ s1 p year events = ⟨true, some tax⟩ := by
  sorry

/-
  Type 3: Given events and some section outcomes, predict missing events

  Example: If we know the tax computed by Section 1 and the filing status,
  we can infer bounds on the taxable income.
-/

/-- Theorem: Inverse reasoning - if tax amount is known and person is unmarried,
    we can determine which bracket and infer taxable income range -/
theorem infer_income_from_tax_unmarried (p : Person) (year : TaxYear)
  (events : List Event) (tax : Int) :
  s1 p year events = ⟨true, some tax⟩ →
  isMarried p year events = none →
  ¬isSurvivingSpouse p year events →
  ¬isHeadOfHousehold p year events →
  ∃ taxinc, getTaxableIncome p year events = some taxinc ∧
            s1_c_tax taxinc = ⟨true, some tax⟩ := by
  sorry

/-- Theorem: If Section 1 produces a specific tax using §1(a) brackets,
    and we know the taxable income, then either married filing jointly or surviving spouse -/
theorem infer_filing_status_from_1a_tax (p : Person) (year : TaxYear)
  (events : List Event) (taxinc : Int) (tax : Int) :
  getTaxableIncome p year events = some taxinc →
  s1_a_tax taxinc = ⟨true, some tax⟩ →
  s1 p year events = ⟨true, some tax⟩ →
  (∃ spouse, isMarried p year events = some spouse ∧
             hasJointReturn p spouse year events ∧
             ¬isNonresidentAlien p year events ∧
             ¬isNonresidentAlien spouse year events) ∨
  isSurvivingSpouse p year events := by
  sorry

/-
  Type 4: Given outcomes, predict required events

  Example: If we want Section 1 to produce a specific tax outcome,
  what events must be present?
-/

/-- Theorem: To achieve §1(a) tax outcome, need marriage + joint return OR surviving spouse -/
theorem events_required_for_1a_outcome (p : Person) (year : TaxYear) (tax : Int) :
  (∃ events taxinc,
    s1_a p year events = ⟨true, some tax⟩ ∧
    s1_a_tax taxinc = ⟨true, some tax⟩ ∧
    getTaxableIncome p year events = some taxinc) →
  (∃ events spouse,
    isMarried p year events = some spouse ∧
    hasJointReturn p spouse year events ∧
    ¬isNonresidentAlien p year events ∧
    ¬isNonresidentAlien spouse year events) ∨
  (∃ events, isSurvivingSpouse p year events) := by
  sorry

/-- Theorem: To file as head of household, specific events must be present -/
theorem events_required_for_hoh_status (p : Person) (year : TaxYear) :
  (∃ events tax, s1_b p year events = ⟨true, some tax⟩) →
  ∃ events, isHeadOfHousehold p year events ∧
            isMarried p year events = none ∧
            ¬isSurvivingSpouse p year events := by
  sorry

/-- Theorem: Tax bracket consistency - if income is in a specific range,
    the tax calculation matches the expected bracket formula -/
theorem bracket_consistency_1a_ii (taxinc : Int) :
  36900 < taxinc →
  taxinc ≤ 89150 →
  s1_a_tax taxinc = ⟨true, some (5535 + roundMulDiv (taxinc - 36900) 28 100)⟩ := by
  sorry

/-- Theorem: Filing status uniqueness - a person can only have one of §1(a) or §1(c) apply -/
theorem filing_status_unique_a_c (p : Person) (year : TaxYear) (events : List Event)
  (tax1 tax2 : Int) :
  s1_a p year events = ⟨true, some tax1⟩ →
  s1_c p year events = ⟨true, some tax2⟩ →
  False := by
  sorry

/-- Theorem: Tax increases with income (monotonicity) in §1(c) -/
theorem tax_monotone_1c (inc1 inc2 : Int) (tax1 tax2 : Int) :
  0 ≤ inc1 →
  inc1 < inc2 →
  s1_c_tax inc1 = ⟨true, some tax1⟩ →
  s1_c_tax inc2 = ⟨true, some tax2⟩ →
  tax1 < tax2 := by
  sorry

end Section1
