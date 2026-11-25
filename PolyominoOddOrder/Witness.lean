module

public import PolyominoOddOrder.Defs

/-!
# Two closed equalities for the paper's sanity examples (`Witness.lean`)

Two definitions of the trusted surface on small inputs, each proved by
`decide` (the kernel evaluates it; no `native_decide`):

* `R 2 6`, the rectangle of 2 by 6 cells, has 12 cells;
* corner 2 of `R 2 6`, the corner opposite `(0, 0)`, is the cell `(1, 5)`.

`Verify.lean` prints their axioms. `Sanity.lean` holds the same two tests
among many others; this file imports only `Defs`, so the import closure of
`Verify.lean` is that of `Main`, this file and `Verify.lean` itself.
-/

@[expose] public section

namespace PolyominoOddOrder.Witness

open PolyominoOddOrder

theorem R_card : (R 2 6).card = 12 := by
  decide

theorem corner_sample : corner 2 6 2 = (1, 5) := by
  decide

end PolyominoOddOrder.Witness
