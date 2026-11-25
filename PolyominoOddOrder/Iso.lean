module

public import PolyominoOddOrder.Grid

/-!
# Foundation 2: grid isometries (`Iso.lean`)

Blueprint unit F. The group structure of `GridIso` (identity,
composition, inverse), the named symmetries of a rectangle (mirror image,
reflection `F`, half turn `H`, transposition, translations), and what an
isometry preserves: adjacency, connectivity, cardinality, congruence.

Sources: `report.md` section 1 ("An isometry is a symmetry of the grid Z^2: a
translation composed with one of the 8 rotations and reflections of the
square"); `report-2.md`, Lemma 9 ("The 8 symmetries of the square either keep
both axis directions or exchange them"); `report-4.md` section 5d (`F` is the
reflection `y -> b - 1 - y` of `R`) and section 5e (`H` is the half turn of
`R`). Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

namespace GridIso

/-! ## Group structure -/

/-- The identity isometry. -/
def one : GridIso := ⟨false, false, false, (0, 0)⟩

/-- `g.comp h` is "first `h`, then `g`". -/
def comp (g h : GridIso) : GridIso where
  swap := xor g.swap h.swap
  negX := xor g.negX (if g.swap then h.negY else h.negX)
  negY := xor g.negY (if g.swap then h.negX else h.negY)
  shift := g.apply h.shift

/-- The inverse isometry. -/
def inv (g : GridIso) : GridIso where
  swap := g.swap
  negX := if g.swap then g.negY else g.negX
  negY := if g.swap then g.negX else g.negY
  shift :=
    (if g.swap then (if g.negY then g.shift.2 else -g.shift.2)
      else (if g.negX then g.shift.1 else -g.shift.1),
     if g.swap then (if g.negX then g.shift.1 else -g.shift.1)
      else (if g.negY then g.shift.2 else -g.shift.2))

@[simp] theorem one_apply (c : Cell) : one.apply c = c := by
  simp [one, apply]

theorem comp_apply (g h : GridIso) (c : Cell) : (g.comp h).apply c = g.apply (h.apply c) := by
  obtain ⟨gs, gx, gy, ⟨a, b⟩⟩ := g
  obtain ⟨hs, hx, hy, ⟨a', b'⟩⟩ := h
  obtain ⟨x, y⟩ := c
  cases gs <;> cases gx <;> cases gy <;> cases hs <;> cases hx <;> cases hy <;>
    simp [comp, apply] <;> omega

theorem inv_apply_apply (g : GridIso) (c : Cell) : g.inv.apply (g.apply c) = c := by
  obtain ⟨gs, gx, gy, ⟨a, b⟩⟩ := g
  obtain ⟨x, y⟩ := c
  cases gs <;> cases gx <;> cases gy <;> simp [inv, apply]

theorem apply_inv_apply (g : GridIso) (c : Cell) : g.apply (g.inv.apply c) = c := by
  obtain ⟨gs, gx, gy, ⟨a, b⟩⟩ := g
  obtain ⟨x, y⟩ := c
  cases gs <;> cases gx <;> cases gy <;> simp [inv, apply]

/-- An isometry is injective on cells. -/
theorem apply_injective (g : GridIso) : Function.Injective g.apply :=
  Function.LeftInverse.injective (inv_apply_apply g)

/-- `c` lies in the image of `S` exactly when its preimage lies in `S`. -/
theorem mem_image_iff (g : GridIso) (S : Finset Cell) (c : Cell) :
    c ∈ S.image g.apply ↔ g.inv.apply c ∈ S := by
  constructor
  · intro h
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 h
    rwa [inv_apply_apply]
  · intro h
    exact Finset.mem_image.2 ⟨_, h, apply_inv_apply g c⟩

/-- The image under a composite is the image of the image. -/
theorem image_comp (g h : GridIso) (S : Finset Cell) :
    S.image (g.comp h).apply = (S.image h.apply).image g.apply := by
  rw [Finset.image_image]
  exact Finset.image_congr fun c _ => comp_apply g h c

/-- Applying `g` and then `g.inv` to a set gives the set back. -/
theorem image_inv_image (g : GridIso) (S : Finset Cell) :
    (S.image g.apply).image g.inv.apply = S := by
  ext c
  constructor
  · intro h
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hd
    rwa [inv_apply_apply]
  · intro h
    exact Finset.mem_image.2 ⟨g.apply c, Finset.mem_image_of_mem _ h, inv_apply_apply g c⟩

/-- An isometry preserves the number of cells. -/
theorem card_image (g : GridIso) (S : Finset Cell) : (S.image g.apply).card = S.card :=
  Finset.card_image_of_injective S g.apply_injective

/-! ## What an isometry preserves -/

/-- An isometry preserves adjacency. -/
theorem adj_apply_iff (g : GridIso) (c d : Cell) : Adj (g.apply c) (g.apply d) ↔ Adj c d := by
  obtain ⟨gs, gx, gy, ⟨a, b⟩⟩ := g
  obtain ⟨x, y⟩ := c
  obtain ⟨x', y'⟩ := d
  cases gs <;> cases gx <;> cases gy <;> simp only [apply, Adj] <;> simp <;> omega

/-- An isometry carries chains to chains. -/
theorem reach_image (g : GridIso) {S : Finset Cell} {c d : Cell} (h : Reach S c d) :
    Reach (S.image g.apply) (g.apply c) (g.apply d) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.tail ih
      ⟨Finset.mem_image_of_mem _ hbc.1, Finset.mem_image_of_mem _ hbc.2.1,
        (adj_apply_iff g _ _).2 hbc.2.2⟩

/-- The image of a connected set is connected. -/
theorem edgeConnected_image (g : GridIso) {S : Finset Cell} (hS : EdgeConnected S) :
    EdgeConnected (S.image g.apply) := by
  intro c hc d hd
  obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hc
  obtain ⟨d', hd', rfl⟩ := Finset.mem_image.1 hd
  exact reach_image g (hS c' hc' d' hd')

/-- The image of a polyomino is a polyomino. -/
theorem isPolyomino_image (g : GridIso) {S : Finset Cell} (hS : IsPolyomino S) :
    IsPolyomino (S.image g.apply) :=
  ⟨hS.1.image _, edgeConnected_image g hS.2⟩

/-! ## Named symmetries of a rectangle -/

/-- The translation by `v`. -/
def translate (v : Cell) : GridIso := ⟨false, false, false, v⟩

/-- The mirror image `x -> a - 1 - x` of `R a b`. -/
def flipX (a : ℤ) : GridIso := ⟨false, true, false, (a - 1, 0)⟩

/-- The reflection `F`: `y -> b - 1 - y` of `R a b` (`report-4.md`, section 5d). -/
def flipY (b : ℤ) : GridIso := ⟨false, false, true, (0, b - 1)⟩

/-- The half turn `H` of `R a b` (`report-4.md`, section 5e). -/
def halfTurn (a b : ℤ) : GridIso := ⟨false, true, true, (a - 1, b - 1)⟩

/-- The transposition `(x, y) -> (y, x)`, which carries `R a b` onto `R b a`. -/
def transpose : GridIso := ⟨true, false, false, (0, 0)⟩

@[simp] theorem translate_apply (v c : Cell) : (translate v).apply c = (c.1 + v.1, c.2 + v.2) := by
  simp [translate, apply]

@[simp] theorem flipX_apply (a : ℤ) (c : Cell) : (flipX a).apply c = (a - 1 - c.1, c.2) := by
  simp [flipX, apply]
  omega

@[simp] theorem flipY_apply (b : ℤ) (c : Cell) : (flipY b).apply c = (c.1, b - 1 - c.2) := by
  simp [flipY, apply]
  omega

@[simp] theorem halfTurn_apply (a b : ℤ) (c : Cell) :
    (halfTurn a b).apply c = (a - 1 - c.1, b - 1 - c.2) := by
  simp [halfTurn, apply]
  omega

@[simp] theorem transpose_apply (c : Cell) : transpose.apply c = (c.2, c.1) := by
  simp [transpose, apply]

/-- The mirror image maps `R a b` onto itself. -/
theorem image_R_flipX (a b : ℤ) : (R a b).image (flipX a).apply = R a b := by
  ext c
  rw [mem_image_iff, mem_R, mem_R]
  simp [flipX, inv, apply]
  omega

/-- The reflection `F` maps `R a b` onto itself. -/
theorem image_R_flipY (a b : ℤ) : (R a b).image (flipY b).apply = R a b := by
  ext c
  rw [mem_image_iff, mem_R, mem_R]
  simp [flipY, inv, apply]
  omega

/-- The half turn maps `R a b` onto itself. -/
theorem image_R_halfTurn (a b : ℤ) : (R a b).image (halfTurn a b).apply = R a b := by
  ext c
  rw [mem_image_iff, mem_R, mem_R]
  simp [halfTurn, inv, apply]
  omega

/-- The transposition maps `R a b` onto `R b a`. -/
theorem image_R_transpose (a b : ℤ) : (R a b).image transpose.apply = R b a := by
  ext c
  rw [mem_image_iff, mem_R, mem_R]
  simp [transpose, inv, apply]
  omega

end GridIso

/-! ## Congruence -/

theorem Congruent.refl (S : Finset Cell) : Congruent S S := by
  have h : GridIso.one.apply = fun c => c := funext GridIso.one_apply
  exact ⟨GridIso.one, by rw [h]; exact Finset.image_id'⟩

theorem Congruent.symm {S T : Finset Cell} (h : Congruent S T) : Congruent T S := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨g.inv, GridIso.image_inv_image g S⟩

theorem Congruent.trans {S T U : Finset Cell} (h : Congruent S T) (h' : Congruent T U) :
    Congruent S U := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨g', rfl⟩ := h'
  exact ⟨g'.comp g, GridIso.image_comp g' g S⟩

/-- Congruent sets have the same number of cells. -/
theorem Congruent.card_eq {S T : Finset Cell} (h : Congruent S T) : T.card = S.card := by
  obtain ⟨g, rfl⟩ := h
  exact GridIso.card_image g S

/-- A set congruent to a polyomino is a polyomino. -/
theorem Congruent.isPolyomino {S T : Finset Cell} (h : Congruent S T) (hS : IsPolyomino S) :
    IsPolyomino T := by
  obtain ⟨g, rfl⟩ := h
  exact GridIso.isPolyomino_image g hS

end PolyominoOddOrder
