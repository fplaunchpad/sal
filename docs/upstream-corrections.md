# Proposed corrections to the posted upstream reports

Prepared 2026-10-29 after Codex's review (`docs/upstream-report-review.md`
in the main tree), and applied the same day as in-place edits of the posted
bodies and comments (KC's choice, since the corrections are to wording and
controls, not to the measured observations); each edited post ends with a
dated line saying what changed, and the live texts are mirrored in the
`upstream-drafts.md` files. The comment texts below were the proposals;
the applied wording differs slightly where it had to fit the body. This
file names upstream threads and stays outside the anonymous artifact.

Every claim below was re-run on the pinned versions on 2026-10-29.

## 1. loro-dev/loro#1240, shape 1: the deleted-highlight variant also fails

Posted text says the variant "where the only highlighted character is
deleted and a character is typed into its place" is correct. It is not.
On 1.17.1 with `hl` expand `both`: insert `a`, highlight it, delete it,
type `X` gives `X` highlighted; the same with `bold` expand `after` gives
`X` plain; `abc`, highlight `b`, delete `b`, type `X` at 1 gives `X`
highlighted; the same with `link` expand `none` gives `aXc` plain.

Comment to post:

> Correction to shape 1. The sentence "and so is the variant where the only
> highlighted character is deleted and a character is typed into its place"
> is wrong: that variant fails in the same way. On 1.17.1 with `hl` set to
> expand `both`, insert `a`, highlight it, delete it and type `X` gives
> `[{"insert":"X","attributes":{"hl":true}}]`; from `abc`, highlight `b`,
> delete `b` and type `X` at 1 gives `X` highlighted between `a` and `c`.
> The controls are the same shapes with `bold` (expand `after`) and `link`
> (expand `none`), which give `X` plain. So shape 1 has two forms, removal
> of the style and deletion of its only character, and one control each.
>
> Two bounds on the rest of the report. Shape 3 assumes that two documents
> with the same display give the same result for the same request; the
> hidden anchors differ, and whether the API promises that is for you to
> say. The closing sentence about the Fugue list should read: no checked
> plain-text version lacked a witness under the strong list specification
> in 800 trials, which is a bounded measurement, not a proof.

## 2. loro-dev/loro#1009: scope of the posted example

The posted script is the expand-after start case with the peer ids
swapped. The claim that the same happens "for every expand setting
including `none`, and at either end" rests on the campaign, not on that
script.

Comment to post:

> One clarification of scope. The script above is the expand-after start
> case, the one this issue reported, with the peer ids swapped to show the
> dependence. The statement that the same ordering decides the outcome for
> every expand setting and at either end comes from a property-based run
> over 1,200 trials, not from this script; the minimal shapes for a
> non-expanding link end and for the crossed case are in the regression
> file of that run and I can post them if useful. The undo residue in the
> original report was not re-run.

## 3. yjs/yjs#828: no guaranteed shared fix, and what "both orders" means

Posted text says "a fix for one is a fix for all". No fix was built or
tested, and boundary ordering (#385) is a different mechanism from marker
reuse and cleanup (#828, #382). Posted text also says the expected document
is what "applying both operations in one of the two orders" gives; the
sequential comparison interprets each edit by the character identities and
anchors it recorded when issued, not by reissuing the numeric index against
a changed document (shape 3's `insert(3, 'z')` cannot be reissued unchanged
after `b` is deleted).

Comment to post:

> Two corrections to the text above, neither to the reproductions.
>
> First, "a fix for one is a fix for all" claims more than these
> reproductions show. I grouped the three shapes because in each a
> formatting marker that another edit relied on was deleted or reused by
> a concurrent operation; they may need separate repairs, and no repair was
> tried. #382 is the overlapping-formats face of the same marker handling.
> #385 additionally involves how a concurrent insertion is ordered against
> a format boundary, which a change to marker ownership alone need not
> affect.
>
> Second, "applying both operations in one of the two orders" means
> applying each edit with the character identities and anchors recorded
> when it was issued, not reissuing the same numeric indices against the
> other replica's document. In shape 3 the insert after `b` stays anchored
> after `b` once `b` is a tombstone, and in that order `z` is bold; in the
> other order the delete removes `b` and `z` is still inserted after it,
> bold. Both orders give the document marked "expected".

Comments to post on #382 and #385, replacing the "same cause" sentence:

> Narrowing the cross-reference above: the three shapes in #828 and this
> one share the marker representation, in which a format's extent is
> decided by marker items and their positions; this issue is the
> overlapping-formats face of it. They may need separate repairs. (#382)

> Narrowing the cross-reference above: this boundary case involves how a
> concurrent insertion is ordered against a format boundary, which is
> related to but not the same mechanism as the marker reuse and cleanup in
> #828; a repair of one need not repair the other. (#385)

## 4. automerge/automerge#1649: the controls change the text, and a cleaner one

Posted text says the control "differs only in a counter"; the first control
keeps `x` in the text and the second omits `z`. A control that changes no
text exists: raise the marking replica's counter with an edit outside the
text (`doc.n = 1` in the same change as the mark). On 3.5.0: with that
edit `h` is bold, without it `h` is plain. Posted text also says Automerge
passes "every concurrent formatting shape on which Yjs fails"; it passes
the shapes tested, the ones in yjs/yjs#828 and #382.

Comment to post:

> Two corrections. The controls above change the text as well as the
> counter (the first keeps `x`, the second has no `z`); what they share
> with the failing runs is the formatting expectation, `h` plain and `x`
> outside the link, under the stated reading. A control that leaves the
> text identical and changes only the counter gives the same flip:
>
> ```js
> import * as A from '@automerge/automerge';
> const show = (d) => JSON.stringify(A.spans(d, ['t']));
> const run = (bump) => {
>   let d1 = A.from({ t: '', n: 0 }, { actor: 'aaaa' });
>   d1 = A.change(d1, (doc) => { A.splice(doc, ['t'], 0, 0, 'a'); });
>   let d2 = A.clone(d1, { actor: 'bbbb' });
>   d1 = A.change(d1, (doc) => {
>     if (bump) doc.n = 1;                                                     // raises the counter; text unchanged
>     A.mark(doc, ['t'], { start: 0, end: 1, expand: 'after' }, 'bold', true);
>   });
>   d2 = A.change(d2, (doc) => { A.splice(doc, ['t'], 0, 0, 'h'); });
>   const m1 = show(A.merge(A.clone(d1), d2)), m2 = show(A.merge(A.clone(d2), d1));
>   return m1 === m2 ? m1 : `${m1} / ${m2}`;
> };
> console.log('with the extra edit   ', run(true));
> console.log('without the extra edit', run(false));
> ```
>
> Output on 3.5.0: with the extra edit `[{"type":"text","value":"ha","marks":{"bold":true}}]`, without it `[{"type":"text","value":"h"},{"type":"text","value":"a","marks":{"bold":true}}]`.
>
> And "every concurrent formatting shape on which Yjs fails" should read
> "the shapes reported in yjs/yjs#828 and #382", which are the ones tested.

## 5. yjs/yjs#829: no correction

The report states the documented guarantee, asks whether intermediate
states are meant to be causally closed, and names provider and
reconnection scenarios as delivery patterns, not as reproduced failures of
those providers. Codex notes that the listed causal prefixes include states
that need the withheld update; that is what "closed under what those
operations were issued after" means, and the text already says the
replica's state is none of them.
