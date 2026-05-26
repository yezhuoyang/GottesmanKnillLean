import Mathlib.Tactic

/-!
# Basic single-qubit Pauli operators and phases
This corresponds to LaTeX section *Definitions of the quantum gates and circuit identities*
(file `GateIdentity.tex`). The concrete 2×2 matrices `I, X, Y, Z, H, P, T, CNOT` from
eq. (`eq:DefOfGate`) and the multiplication identities from (`eq:PauliMulti`,
`eq:SquareIdentity`) are encoded *algebraically*: a `Pauli1` value carries only the
*letter* `I/X/Y/Z`, while overall ±1, ±i factors live in a separate `Phase` type. The
matrix form is never needed in the rest of the development.

This is the only file where we hand-write the multiplication table; downstream we
just reason about the resulting algebraic structure.
-/

namespace GottesmanKnill

/-- The four single-qubit Pauli letters `I, X, Y, Z`. No phase information here. -/
inductive Pauli1 : Type
  | I : Pauli1
  | X : Pauli1
  | Y : Pauli1
  | Z : Pauli1
  deriving DecidableEq, Repr

/-- The four scalar phases that can appear in front of a Pauli string:
`+1, -1, +i, -i`. This is the subgroup `⟨i⟩ ≤ ℂ*` of fourth roots of unity. -/
inductive Phase : Type
  | one    : Phase   -- `+1`
  | negOne : Phase   -- `-1`
  | i      : Phase   -- `+i`
  | negI   : Phase   -- `-i`
  deriving DecidableEq, Repr

namespace Phase

/-- Multiplication of phases. Worked out fully here as scaffolding —
later proofs about Phase only need this `def`. Closed form: regard
`one=0, i=1, negOne=2, negI=3 (mod 4)` and add. -/
def mul : Phase → Phase → Phase
  | one,    p      => p
  | p,      one    => p
  | negOne, negOne => one
  | negOne, i      => negI
  | negOne, negI   => i
  | i,      negOne => negI
  | i,      i      => negOne
  | i,      negI   => one
  | negI,   negOne => i
  | negI,   i      => one
  | negI,   negI   => negOne

/-- The phase inverse: `(+1)⁻¹ = +1`, `(-1)⁻¹ = -1`, `i⁻¹ = -i`, `(-i)⁻¹ = i`. -/
def inv : Phase → Phase
  | one    => one
  | negOne => negOne
  | i      => negI
  | negI   => i

instance : Mul Phase := ⟨mul⟩
instance : One Phase := ⟨one⟩
instance : Inv Phase := ⟨inv⟩

/--
Phase` is a (commutative) group under `mul`/`one`/`inv`.
-/
instance : CommGroup Phase where
  mul         := mul
  one         := one
  inv         := inv
  mul_assoc   := by
       intro a b c;
       cases a <;> cases b <;> cases c <;> rfl
  one_mul     := by
       intro a;
       cases a <;> rfl
  mul_one     := by
       intro a
       cases a <;> rfl
  inv_mul_cancel := by
        intro a; cases a <;> rfl
  mul_comm    := by
        intro a b; cases a <;> cases b <;> rfl
end Phase

/-! ### Single-qubit Pauli multiplication

The defining identities in `eq:PauliMulti`:

  X*Y =  i Z,   Y*Z =  i X,   Z*X =  i Y
  Y*X = -i Z,   Z*Y = -i X,   X*Z = -i Y

together with `X² = Y² = Z² = I`, fully determine the multiplication of two
single-qubit Paulis. The product comes with a phase, so the result type is
`Phase × Pauli1`.
-/

namespace Pauli1

/-- The product of two single-qubit Paulis: returns `(phase, letter)`.
This is the algebraic content of equations (`eq:SquareIdentity`, `eq:PauliMulti`)
in `GateIdentity.tex`.
 -/
def mul : Pauli1 → Pauli1 → Phase × Pauli1
  -- I is the identity.
  | I, q => (Phase.one, q)
  | q, I => (Phase.one, q)
  -- Squares.
  | X, X => (Phase.one, I)
  | Y, Y => (Phase.one, I)
  | Z, Z => (Phase.one, I)
  -- Mixed products: X·Y =  iZ,   Y·X = -iZ  (worked out as scaffolding)
  | X, Y => (Phase.i,    Z)
  | Y, X => (Phase.negI, Z)
  --   Y*Z =  i X     Z*Y = -i X
  --   Z*X =  i Y     X*Z = -i Y
  | Y, Z => (Phase.i,  X)
  | Z, Y => (Phase.negI, X)
  | Z, X => (Phase.i, Y)
  | X, Z => (Phase.negI, Y)

/-- The single-qubit "commutativity index" `q ∈ {0,1}` from eq:`defq`:
`q = 0` if `a*b = b*a`, `q = 1` if `a*b = -b*a`. For single-qubit Paulis,
two distinct non-identity letters always anticommute, and anything involving
`I` commutes. -/
def commIdx : Pauli1 → Pauli1 → Bool
  | I, _ => false
  | _, I => false
  | a, b => if a = b then false else true

/--
Single-qubit Paulis either commute or anticommute.
That is, if `mul a b = (φ, c)` and `mul b a = (ψ, c')`, then `c = c'` and
`ψ = if commIdx a b then -φ else φ`.
-/
theorem mul_comm_or_anticomm (a b : Pauli1) :
    (mul a b).2 = (mul b a).2 ∧
    (mul b a).1 = if commIdx a b then Phase.negOne * (mul a b).1 else (mul a b).1 := by
    constructor
    . -- left
       cases a <;> cases b <;> try rfl
    . -- right
       cases a <;> cases b <;> try rfl
end Pauli1

end GottesmanKnill
