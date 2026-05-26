import GottesmanKnill.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# The n-qubit Pauli group `P_n`

Corresponds to LaTeX section `PauliGroup.tex`.

Following the *Pauli group representation* theorem (`thm:PauliGroupReprep`),
every element of `P_n` has the form `a_0 ⊗_{i=1}^n a_i` with `a_0 ∈ {±1, ±i}`
and each `a_i ∈ {I, X, Y, Z}`. We use that representation as the *definition*:
a `PauliOp n` value is just a pair `(phase, qubit-wise letters)`.

The point of this file is to give:

* the carrier type `PauliOp n`,
* the multiplication that makes it a group,
* the statements (only — proofs are exercises) of
    - `card_PauliOp`        : `|P_n| = 4 · 4^n   = 4^(n+1)`           (`thm:PauliGroup`)
    - `mul_comm_or_anticomm`: any two elements (anti)commute          (`thm:Paulicommute`)
    - `commCriterion`       : the (anti)commutation criterion         (`thm:Criterion`)
    - `sq_eq_pmI`           : `A² = ±I`                                (`thm:Paulisquare`)
-/

namespace GottesmanKnill

open Phase

/-- An element of the `n`-qubit Pauli group, in the general representation
`a_0 ⊗_{i=1}^n a_i` of `thm:PauliGroupReprep`. -/
structure PauliOp (n : ℕ) where
  /-- The scalar prefactor `a_0 ∈ {±1, ±i}`. -/
  phase : Phase
  /-- The qubit-wise Pauli letters `a_1, …, a_n`, one per qubit. -/
  ops   : Fin n → Pauli1
  deriving DecidableEq

namespace PauliOp

variable {n : ℕ}

/-- The identity element `+1 · I ⊗ … ⊗ I`. -/
def one : PauliOp n := { phase := Phase.one, ops := fun _ => Pauli1.I }

/-- Multiplication of two `n`-qubit Pauli operators.

The qubit-wise product `(a_i, b_i) ↦ Pauli1.mul a_i b_i = (φ_i, c_i)` produces
a per-qubit phase `φ_i` that must be folded into the global phase.

This is the construction underlying eq:`multAB`. -/
def mul (a b : PauliOp n) : PauliOp n :=
  -- Strategy:
  --   1. for each `i`, let `(φ_i, c_i) := Pauli1.mul (a.ops i) (b.ops i)`
  --   2. the new global phase is `a.phase * b.phase * ∏_i φ_i`
  --   3. the new letters are `c_i`
  -- Mathlib's `Finset.univ.prod` gives us the phase product.
  let perQubit : Fin n → Phase × Pauli1 := fun i => Pauli1.mul (a.ops i) (b.ops i)
  { phase := a.phase * b.phase * (Finset.univ.prod fun i => (perQubit i).1)
  , ops   := fun i => (perQubit i).2 }

/-- The inverse of a Pauli operator.

**TODO(you).** Fill in the data. Hint: each single-qubit Pauli letter is its
own inverse (since `X² = Y² = Z² = I`), but you still have to choose the
phase so that `a * inv a = one`. Work this out using `a.phase`'s inverse and
the per-qubit phase from `Pauli1.mul (a.ops i) (a.ops i)`. -/
def inv (a : PauliOp n) : PauliOp n :=
  sorry  -- TODO(you): construct the inverse explicitly.

instance : One (PauliOp n) := ⟨one⟩
instance : Mul (PauliOp n) := ⟨mul⟩
instance : Inv (PauliOp n) := ⟨inv⟩

/-- **TODO(you).** Show `PauliOp n` is a group.

Hints:
* `mul_assoc` reduces to associativity in `Phase` and to associativity of
  `Pauli1.mul` at every coordinate. Both should follow from `cases` /
  `decide` once `Pauli1.mul` is filled in.
* `one_mul`, `mul_one` are essentially the `I, _ | _, I` rows of `Pauli1.mul`.
* `mul_left_inv` follows from your construction of `inv`.
-/
instance : Group (PauliOp n) where
  mul          := mul
  one          := one
  inv          := inv
  mul_assoc    := by sorry  -- TODO(you): use `Phase` group laws + `Pauli1.mul` associativity.
  one_mul      := by sorry  -- TODO(you)
  mul_one      := by sorry  -- TODO(you)
  inv_mul_cancel := by sorry  -- TODO(you)

/-! ### The "general Pauli representation" theorems

In our setup these are trivial *by definition*, since `PauliOp n` is already
in the `(phase, fun i => letter)` form. We still state them so the rest of
the development can quote `thm:PauliGroupReprep` / `thm:PauliGroupReprepInverse`
explicitly. -/

/-- Every Pauli operator has a phase and a per-qubit letter assignment.
This is `thm:PauliGroupReprep` — true by definition in our encoding. -/
theorem exists_rep (a : PauliOp n) :
    ∃ (p : Phase) (f : Fin n → Pauli1), a = { phase := p, ops := f } := by
  -- TODO(you): trivial; should follow from `⟨a.phase, a.ops, rfl⟩`.
  sorry

/-- Conversely, any `(phase, letters)` data really is an element of `P_n`.
This is `thm:PauliGroupReprepInverse` — also trivial in our encoding.
(In the LaTeX, it asks you to express the `±1, ±i` phase as a product of
generators; that is automatic here.) -/
theorem of_rep (p : Phase) (f : Fin n → Pauli1) :
    ({ phase := p, ops := f } : PauliOp n) = { phase := p, ops := f } := rfl

/-! ### Cardinality: `|P_n| = 4 · 4^n` (`thm:PauliGroup`) -/

instance : Fintype (PauliOp n) := by
  -- TODO(you): derive via `Fintype` on the product `Phase × (Fin n → Pauli1)`.
  -- Hint: define a bijection to that product, then use `Fintype.ofEquiv`,
  -- or use the `deriving Fintype` machinery if available.
  sorry

/-- `thm:PauliGroup`: `|P_n| = 4^(n+1)`. -/
theorem card_PauliOp : Fintype.card (PauliOp n) = 4 ^ (n + 1) := by
  -- TODO(you): once the `Fintype` instance is in place, count via the product:
  -- `|Phase| = 4`, `|Fin n → Pauli1| = 4^n`, hence `|PauliOp n| = 4 · 4^n = 4^(n+1)`.
  sorry

/-! ### Commutation theory (`thm:Paulicommute`, `thm:Criterion`) -/

/-- The total commutativity index `Σ_i q_i` from eq:`defq`, taken mod 2.
True means the two operators *anticommute*. -/
def commParity (a b : PauliOp n) : Bool :=
  -- TODO(you): take XOR over all qubit positions of `Pauli1.commIdx (a.ops i) (b.ops i)`.
  -- Hint: `Finset.univ.fold xor false (fun i => Pauli1.commIdx (a.ops i) (b.ops i))`
  -- or equivalently `((Finset.univ.filter ...).card % 2 = 1)`.
  sorry

/-- `thm:Paulicommute` + `thm:Criterion` (combined):
any two Pauli operators either commute or anticommute, and which one is
determined exactly by `commParity`.

Hint for the proof:
* expand `a * b` and `b * a` using `mul`;
* use single-qubit `mul_comm_or_anticomm` from `Basic.lean` to relate
  the per-qubit phase factors;
* the products differ by `(-1)^(Σ q_i)`. -/
theorem mul_comm_or_anticomm (a b : PauliOp n) :
    if commParity a b then a * b = (⟨Phase.negOne, fun _ => Pauli1.I⟩ : PauliOp n) * (b * a)
    else a * b = b * a := by
  sorry  -- TODO(you)

/-! ### Square of a Pauli operator (`thm:Paulisquare`) -/

/-- `thm:Paulisquare`: the square of any Pauli operator is `±I`.
We state it as: `a * a = { phase := σ , ops := fun _ => I }` for some `σ ∈ {±1}`. -/
theorem sq_eq_pmI (a : PauliOp n) :
    ∃ σ : Phase, (σ = Phase.one ∨ σ = Phase.negOne) ∧
      a * a = { phase := σ, ops := fun _ => Pauli1.I } := by
  -- Hint: every single-qubit `a_i * a_i` is `(±1, I)`; combine the per-qubit
  -- phases with `a.phase ^ 2`. Note `Phase.i * Phase.i = Phase.negOne`, so
  -- `a.phase^2 ∈ {one, negOne}` automatically.
  sorry  -- TODO(you)

/-! ### Mutually commutative subsets (`df:mutialcomset`, `thm:paulinormalsub`,
`thm:largestPSet`)

We only *state* these — proofs are exercises. -/

/-- `df:mutialcomset`: `S ⊆ P_n` is mutually commutative iff every pair commutes. -/
def MutualCommSet (S : Set (PauliOp n)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a * b = b * a

/-- `thm:largestPSet`: the largest mutually commutative subset of `P_n` has
size exactly `2^n`. -/
theorem largest_mutual_comm_card :
    ∃ (S : Finset (PauliOp n)),
      MutualCommSet (S : Set (PauliOp n)) ∧ S.card = 2 ^ n ∧
      (∀ T : Finset (PauliOp n), MutualCommSet (T : Set (PauliOp n)) → T.card ≤ 2 ^ n) := by
  sorry  -- TODO(you): induction on `n`, following the LaTeX proof.

end PauliOp

end GottesmanKnill
