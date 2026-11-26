# Five congruent copies of a non-rectangular polyomino do not tile a rectangle (`PolyominoOddOrder`)

Lean 4 + Mathlib formalization of 7 statements on tilings of a rectangle of
unit cells by congruent copies of one polyomino, rotations and reflections allowed.
Corollary A19 is proved in Lean: no rectangle is tiled by exactly five congruent copies of a polyomino that is not a rectangle.
Companion paper: No Rectangle Is Tiled by Five Congruent Copies of a Non-Rectangular Polyomino (https://mathdiscoveries.org/results/polyomino-odd-order).

AI research agents built and directed by Tyler B. Hughes generated and checked this work.
No human mathematician has yet refereed the proof.

## Scope

- Proved in Lean: 7 of 7 statements, all witnessed, with the axioms `propext`, `Quot.sound` and
  `Classical.choice` only.
- *Witnessed* means that `PolyominoOddOrder/Sanity.lean` gives an example meeting the
  hypotheses of the statement.
- Corollary A19 (statement 7 below) answers the question that A. Winslow lists as Open
  Problem 11 in the author's version of "Some Open Problems in Polyomino Tilings"
  (DLT 2018): "Is there a polyomino of order 5?". The Springer version of record is
  unread `[to check]`. The notion of order is not defined in this package; what is
  proved is the Lean statement of A19.
- Theorem 62 (three copies) is printed prior work; the proof here is a second proof.
- Internal theorems, not compared statements and not counted: `corners_in_distinct_tiles`,
  `sides_are_intervals`, `corner_tile_sides` and `free_tile_one_side` (Corollary 63,
  Proposition 57 (a) and (b), and Corollary 59 with Proposition 60 of the companion
  work). They are steps of the proof of A19; `Verify.lean` prints their axioms.
- Theorem 21 has a search without hits, at a given number of cells, as a hypothesis. The
  search results of the companion paper (its C5-T statements) are external to this
  package: no search is run or checked in Lean.

## The compared statements (`Challenge.lean`)

1. `PolyominoOddOrder.corollary1a_crossing` (Corollary 1a (crossing)): Let a, b >= 2. If S is a connected subset of R meeting both the left and the right column, and S' is a connected subset of R meeting both the bottom and the top row, then S and S' share a cell.
2. `PolyominoOddOrder.lemma2_no_opposite_corners` (Lemma 2 (no tile holds two opposite corners)): No tile contains two opposite corner cells of R. (Setting: P is a polyomino, k >= 2, and T_1, ..., T_k is a k-copy tiling of R(a, b) by P.)
3. `PolyominoOddOrder.lemma3_adjacent_corners_full_row` (Lemma 3 (two adjacent corners force the whole side)): Suppose a tile T contains the two corner cells (0, 0) and (a - 1, 0). Then T contains every cell of row 0. (Setting: P is a polyomino, k >= 2, and T_1, ..., T_k is a k-copy tiling of R(a, b) by P.)
4. `PolyominoOddOrder.theorem62_no_three_copy_tiling` (Theorem 62 (three copies)): No rectangle is tiled by exactly three congruent non-rectangular polyominoes (grid isometries, reflections included).
5. `PolyominoOddOrder.theorem21_search_bridge` (Theorem 21 (what a search without hits proves)): Fix n. Suppose that, over all rectangles and boxes allowed in section 1, no tuple of I(5), H1(5), H2(5), H1(3), H2(3) has a proper solution that is not a rectangle. Then no rectangle is tiled by exactly 3, and none by exactly 5, congruent copies of a non-rectangular polyomino with n cells.
6. `PolyominoOddOrder.theoremA18_no_case_one_tiling` (Theorem A18 (case (I) does not occur)): Let P be a polyomino that is not a rectangle. There is no 5-copy tiling T_1, ..., T_5 of a rectangle R(a, b) by P in which the four corner cells of R lie in four distinct tiles.
7. `PolyominoOddOrder.corollaryA19_no_five_copy_tiling` (Corollary A19 (five copies)): No rectangle is tiled by exactly five congruent copies of a non-rectangular polyomino.

`Challenge.lean` holds the definitions and the statements and imports Mathlib only.
`Solution.lean` proves the same statements from the library `PolyominoOddOrder`.
Comments that name `Spec.lean` mean `Challenge.lean`. Comments that name `BLUEPRINT.md`,
`SPEC-CHANGES.md`, `report.md`, `report-2.md`, `report-3.md`, `report-4.md` or
`report-A2.md` mean working papers that are not part of this package.

## Prior work

- I. N. Stewart and A. Wormstein, "Polyominoes of order 3 do not exist", J. Combin. Theory
  Ser. A 61 (1992), 130-136. Read in full: if three congruent copies of a connected
  polyomino tile a rectangle, the polyomino is itself rectangular. It contains Theorem 62.
- S. J. Maltby, "Trisecting a rectangle", J. Combin. Theory Ser. A 66 (1994). Read in full
  by an earlier agent unit of this work: it generalises the three-copy result to all
  trisections of a rectangle.
- A. Winslow, "Some Open Problems in Polyomino Tilings", DLT 2018, 74-82. Read in full in
  the author's copy, where Open Problem 11 is "Is there a polyomino of order 5?". The
  Springer version is unread `[to check]`.
- M. Reid, "Tiling Rectangles and Half Strips with Congruent Polyominoes", J. Combin. Theory
  Ser. A 80 (1997), 106-123. Read in the author's preprint: rectangles tiled by an odd
  number of copies.
- A. Talon, thesis, arXiv:2002.11615, chapter 4 read: page 96 says it is not known whether
  there are polyominoes of order 5.
- An exhaustive computer search in the repository
  [fransys-code/polyomino-odd-rectangles](https://github.com/fransys-code/polyomino-odd-rectangles)
  (2026-11-22), README read: no non-rectangular polyomino with at most 24 cells tiles a
  rectangle with exactly 5, 7 or 9 copies (its French summary says that size 24 is still
  running). It calls the general question open and says the search has not been checked by a
  third party.
- A comment by "Zomulgustar" on MathOverflow question 11753 (2016-04-27), read in full: an
  exhaustive search of the non-rectangular polyominoes with at most 13 cells found no rectangle
  tiled by 5, 7 or 9 copies, with "a few 13-ominos left".
- Squares cut into five congruent pieces. A 2022 comment in the same MathOverflow thread says that
  the case of five pieces "was resolved negatively in a paper" and links to L. Yuan, C. T. Zamfirescu
  and T. I. Zamfirescu, "Dissecting the square into five congruent parts", Discrete Math. 339 (2016),
  unread `[to check]`. H. Rao, L. Ren and Y. Wang, "Dissecting a square into congruent polygons",
  Discrete Math. Theor. Comput. Sci. 22 (2020) (arXiv version 3 read), and G. L. Maldonado and
  E. Roldán-Pensado, "Dissecting the square into seven or nine congruent parts", Discrete Math.
  (2022) (arXiv version 4 read; published version `[to check]`), report that it proves, for five
  tiles, that a square tiled by
  congruent copies of a convex polygon is tiled by rectangles. Maldonado and Roldán-Pensado report
  that a conjecture attributed to Danzer, for five congruent polygons that need not be convex,
  remains open. A polyomino that is not a rectangle is not convex, so these results do not cover
  Corollary A19.

The other statements were not found in the searches logged on 2026-11-25 and 2026-11-26 (arXiv, OEIS,
CORE, zbMATH Open, OpenAlex with the works citing Stewart and Wormstein, Winslow and Reid, Google
Scholar, Stack Exchange, GitHub and pages read by hand). Not searched: the free text of Semantic
Scholar (HTTP 429), the full text of CORE (titles and abstracts only), MathSciNet, ScienceDirect and
Springer Link. Unread: Reid,
"Many L-Shaped Polyominoes Have Odd Rectangular Packings" (2014) `[to check]`; Jepsen, Vaughn
and Brantley, "Orders of L-shaped Polyominoes" (2003-2004) `[to check]`; Yuan, Zamfirescu and
Zamfirescu, "Dissecting the square into five congruent parts" (2016) `[to check]`; Golomb,
*Polyominoes*, chapter 8 `[to check]`; Bernat, "Quelques questions ouvertes sur les
polyominos" (2013) `[to check]`; a thesis of the University of Central Florida, "Tiling with
Polyominoes, Polycubes, and Rectangles" (2015) `[to check]`.

## Build

```sh
lake exe cache get
lake build
lake build PolyominoOddOrder.Sanity PolyominoOddOrder.Verify
```

The last line builds the non-vacuity receipts and prints the axioms of each statement
and of the four internal theorems.

## License

Apache-2.0 (see `LICENSE`).
