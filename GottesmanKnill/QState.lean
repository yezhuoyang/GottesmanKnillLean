import GottesmanKnill.PauliGroup
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Abstract quantum states and unitary operators on `n` qubits

We deliberately do *not* model an `n`-qubit state as `(Fin n → Bool) → ℂ` (or
`ℂ^(2^n)`) — the paper's proof only ever uses:

* a group of unitaries `U_n` acting on the state space, and
* the relation "`G` stabilizes `ψ`", meaning `G ψ = ψ`.

So we introduce both as **axiomatized** primitives, postulating just enough that the
Gottesman–Knill development goes through. This mirrors the "Heisenberg picture"
philosophy of the paper: one rarely needs the actual amplitudes.

The concrete instantiation (Hilbert space `ℂ^(2^n)` with the standard matrix
action) is left as a possible future development that proves the axioms hold.
-/

namespace GottesmanKnill

/-- An abstract `n`-qubit pure quantum state. -/
axiom QState : ℕ → Type

/-- An abstract unitary operator on `n` qubits. This is the carrier of the
group `U_n`. -/
axiom Unitary : ℕ → Type

/-- `U_n` is a group. -/
axiom Unitary.instGroup (n : ℕ) : Group (Unitary n)
attribute [instance] Unitary.instGroup

/-- A unitary acts on a quantum state. We use `•` (the standard Mathlib notation
for `MulAction`). -/
axiom Unitary.instMulAction (n : ℕ) : MulAction (Unitary n) (QState n)
attribute [instance] Unitary.instMulAction

/-! ### Pauli operators are unitaries

Every formal `PauliOp n` element should be realisable as a concrete unitary
on `QState n`. We axiomatize this as a group homomorphism.

(In a concrete model with `QState n = ℂ^(2^n)`, this would be the actual
Kronecker-product matrix; the axiomatization here makes the rest of the
development independent of that choice.) -/

/-- Embedding of the algebraic Pauli group into the unitary group. -/
axiom PauliOp.toUnitary {n : ℕ} : PauliOp n →* Unitary n

/-- Convenient infix: `a •ₚ ψ := PauliOp.toUnitary a • ψ`. -/
scoped notation:73 a " •ₚ " ψ => (PauliOp.toUnitary a) • ψ

namespace PauliOp

variable {n : ℕ}

/-- `+1·I⊗…⊗I` acts as the identity on every state. -/
theorem one_smul_state (ψ : QState n) : ((1 : PauliOp n) •ₚ ψ) = ψ := by
  -- TODO(you): use `MonoidHom.map_one` to get `toUnitary 1 = 1`, then `one_smul`.
  sorry

/-- `(a * b) ψ = a (b ψ)`. -/
theorem mul_smul_state (a b : PauliOp n) (ψ : QState n) :
    ((a * b) •ₚ ψ) = (a •ₚ (b •ₚ ψ)) := by
  -- TODO(you): use `MonoidHom.map_mul` and `mul_smul`.
  sorry

end PauliOp

/-! ### The standard computational basis state `|0⟩^⊗ⁿ`

In the paper, the simulation always starts in `|0⟩^⊗n`. We introduce it as a
distinguished element, axiomatized by the fact that each `Z_i` stabilizes
it (the content of `thm:stabilizerof0`). -/

/-- The all-zeros computational basis state. -/
axiom QState.zero (n : ℕ) : QState n

/-- The `i`-th single-qubit Pauli-Z, embedded as an `n`-qubit Pauli operator.

**TODO(you).** Construct it. Hint: `phase := one`, `ops := fun j => if j = i then Z else I`. -/
def PauliOp.singleZ {n : ℕ} (i : Fin n) : PauliOp n :=
  sorry  -- TODO(you)

/-- `Z_i |0⟩^⊗n = |0⟩^⊗n` for every qubit `i`. This is the *axiom* characterizing
`QState.zero`; everything we say later about the stabilizer of `|0⟩^⊗n`
ultimately bottoms out here. -/
axiom QState.zero_stabilized_by_Z {n : ℕ} (i : Fin n) :
    ((PauliOp.singleZ i) •ₚ QState.zero n) = QState.zero n

end GottesmanKnill
