import GottesmanKnill.QState

/-!
# The stabilizer subgroup of a quantum state

Corresponds to LaTeX section `Stabilizer.tex`.

For a state `ψ : QState n` we define

  Stab(ψ) := { G ∈ P_n | G ψ = ψ }

and prove that:

* `Stab(ψ)` is closed under multiplication and inverses (`lem:mulclosestab`,
  `lem:stabinverse`),
* hence it is a subgroup of `P_n` (`thm:Commute`),
* and in fact an Abelian subgroup (also `thm:Commute`).

We then state — but do not prove — the eigenspace corollaries
`cor:commtSame` and `cor:sameigenSpace`.

The "equivalence in the sense of action on `ψ`" used in `thm:Commute` is encoded
*not* by passing to a quotient, but by directly asserting commutativity:
two Paulis that both stabilize `ψ` automatically commute as Paulis (the proof
in the LaTeX shows `AB ψ = ψ = BA ψ`, but uses the additional structure that
PauliOps either commute or anticommute globally). This is the content of
`cor:commtSame`. -/

namespace GottesmanKnill

variable {n : ℕ}

/-- The set of Pauli operators that stabilize `ψ`: `G ψ = ψ`. -/
def Stab (ψ : QState n) : Set (PauliOp n) :=
  {G : PauliOp n | (G •ₚ ψ) = ψ}

namespace Stab

/-- `lem:mulclosestab`: if both `A` and `B` stabilize `ψ`, so does `A*B`. -/
theorem mul_mem {ψ : QState n} {A B : PauliOp n}
    (hA : A ∈ Stab ψ) (hB : B ∈ Stab ψ) : A * B ∈ Stab ψ := by
  -- Hint: `(A*B) ψ = A (B ψ) = A ψ = ψ`. Use `PauliOp.mul_smul_state`.
  sorry  -- TODO(you)

/-- The identity Pauli always stabilizes `ψ`. -/
theorem one_mem (ψ : QState n) : (1 : PauliOp n) ∈ Stab ψ := by
  -- Hint: `PauliOp.one_smul_state`.
  sorry  -- TODO(you)

/-- `lem:stabinverse`: stabilizers are closed under inverse. -/
theorem inv_mem {ψ : QState n} {A : PauliOp n} (hA : A ∈ Stab ψ) :
    A⁻¹ ∈ Stab ψ := by
  -- Hint: `A⁻¹ ψ = A⁻¹ (A ψ) = (A⁻¹ * A) ψ = 1 ψ = ψ`.
  sorry  -- TODO(you)

end Stab

/-- `thm:Commute` (group part): `Stab(ψ)` is a subgroup of `P_n`.

**TODO(you).** Bundle the three closure lemmas into a `Subgroup`.
Hint: `Subgroup.mk` or `Subgroup.ofGroupHom` machinery; or just fill in the
fields directly using `Stab.mul_mem`, `Stab.one_mem`, `Stab.inv_mem`. -/
def StabSubgroup (ψ : QState n) : Subgroup (PauliOp n) where
  carrier   := Stab ψ
  mul_mem'  := by sorry  -- TODO(you)
  one_mem'  := by sorry  -- TODO(you)
  inv_mem'  := by sorry  -- TODO(you)

/-- `thm:Commute` (commutativity part): `Stab(ψ)` is *Abelian*.

In the paper, this uses two ingredients:
1. any two Paulis either commute or anticommute (`thm:Paulicommute`);
2. two stabilizers of the same state cannot anticommute, because then `AB ψ = ψ`
   and `BA ψ = -AB ψ = -ψ ≠ ψ`.

**TODO(you).** Translate this argument. You'll likely need a lemma along the
lines of "if `A • ψ = ψ` and `A •ₚ ψ = - (A •ₚ ψ)` then `ψ = -ψ`, contradiction" —
which in turn requires an axiom that the global `-1` phase does *not* act as
the identity on every state. Make that an explicit assumption or axiom; see
the discussion in the LaTeX after `lem:realconstantPauli`. -/
theorem stab_comm {ψ : QState n} {A B : PauliOp n}
    (hA : A ∈ Stab ψ) (hB : B ∈ Stab ψ) : A * B = B * A := by
  sorry  -- TODO(you)

/-! ### Real-phase property (`lem:realconstantPauli`)

A stabilizer must have phase `±1` (never `±i`), because eigenvalues of a
Hermitian operator are real and `Aψ = ψ` makes `ψ` a `+1`-eigenvector. -/

/-- `lem:realconstantPauli`. -/
theorem stab_phase_real {ψ : QState n} {A : PauliOp n} (hA : A ∈ Stab ψ) :
    A.phase = Phase.one ∨ A.phase = Phase.negOne := by
  sorry  -- TODO(you): see the LaTeX argument via `thm:Paulieigen`.

/-! ### Eigenspace corollaries (`cor:commtSame`, `cor:sameigenSpace`)

These are statements about *shared* eigenspaces of commuting Hermitian Paulis.
In our abstract setup we don't have eigenspaces as such, but we can state the
relevant fact in terms of the existence of a common stabilized state. -/

/-- `cor:commtSame` (∀-direction): if `A` and `B` both stabilize some state,
they commute. (The other direction `commute → ∃ ψ both stabilize` lives at the
level of the concrete model; we state it as a hypothesis-bearing theorem.) -/
theorem comm_of_stab_common {A B : PauliOp n}
    (h : ∃ ψ : QState n, A ∈ Stab ψ ∧ B ∈ Stab ψ) : A * B = B * A := by
  sorry  -- TODO(you)

end GottesmanKnill
