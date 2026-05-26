import GottesmanKnill.Heisenberg

/-!
# Gottesman–Knill theorem

Corresponds to LaTeX file `maintheorem.tex`.

The theorem says: a quantum computation consisting of
1. state preparation in the computational basis,
2. Clifford gates,
3. Pauli measurements,
4. classical control,
can be simulated classically in `O(m n²)` time and `O(n²)` space, where
`m` is the number of gates and `n` the number of qubits.

In this Lean file we encode the *correctness* half (the simulation faithfully
tracks the quantum state via its stabilizer). The complexity claim is not
formalized at the level of running time — instead we capture it through

* the size of the data we need to maintain — exactly `n` Pauli generators,
  each represented by `O(n)` symbols, hence `O(n²)` space, and
* the cost of each update — a `PauliOp n` is updated by *one* Clifford map,
  which acts locally on at most 2 qubits, hence `O(n)` (in fact `O(1)`) per
  gate, hence `O(mn²)` for `m` gates.

For the formal statement, we use a `SimResult` that wraps the simulated
generators together with the postcondition `Stab(ψ_m) = ⟨…⟩`.
-/

namespace GottesmanKnill

variable {n : ℕ}

/-- A *Clifford circuit* on `n` qubits is just a finite sequence of Clifford gates.
This is the input to the Gottesman–Knill simulator. -/
abbrev CliffordCircuit (n : ℕ) := List (Clifford n)

/-- The quantum state produced by a Clifford circuit starting from `|0⟩^⊗n`. -/
noncomputable def CliffordCircuit.output (C : CliffordCircuit n) : QState n :=
  (C.map (fun g => (g : Unitary n))).foldr (· * ·) 1 • QState.zero n

/-- The *stabilizer tableau* produced by classical simulation: the `n` generators
of `Stab(output C)`. -/
noncomputable def CliffordCircuit.tableau (C : CliffordCircuit n) : Fin n → PauliOp n :=
  GottesmanKnill.tableau C

/-! ### Main theorem (correctness)

The Gottesman–Knill theorem, stated as: the classically computed `tableau C`
really generates the stabilizer of the quantum output state. Together with
`thm:oneonemap` (i.e. `stab_injective` in `StabilizerState.lean`), this means
the output state is *uniquely determined* by the `n` Pauli operators we
maintained — which is the whole point of the simulation. -/

/-- `thm:Gottesman-Knill` (correctness half).

For every `n`-qubit Clifford circuit `C`, the classical simulation
`tableau C : Fin n → PauliOp n` correctly tracks the stabilizer of the
output state `output C`. Each step of the simulation only updates `n`
Pauli operators (each `O(n)` bits), hence the total data is `O(n²)`
and the per-step cost is `O(n)`, giving `O(mn²)` total time for an
`m`-gate circuit. -/
theorem gottesman_knill (C : CliffordCircuit n) :
    StabSubgroup (CliffordCircuit.output C) =
      Subgroup.closure (Set.range (CliffordCircuit.tableau C)) := by
  sorry  -- TODO(you): direct corollary of `stab_generated_by_tableau`.

/-- Uniqueness corollary: the output state is determined by the tableau.

(`thm:oneonemap` + `gottesman_knill`.) -/
theorem gottesman_knill_unique
    (C₁ C₂ : CliffordCircuit n)
    (h : Subgroup.closure (Set.range (CliffordCircuit.tableau C₁)) =
         Subgroup.closure (Set.range (CliffordCircuit.tableau C₂))) :
    CliffordCircuit.output C₁ = CliffordCircuit.output C₂ := by
  sorry  -- TODO(you): combine `gottesman_knill` (for both circuits) with `stab_injective`.

/-! ### Complexity (`maintheorem.tex` complexity claim)

The paper claims `O(mn²)` time and `O(n²)` space. We make this precise via two
*concrete* cost functions, then bound them.

**Space.** A single `PauliOp n` carries `n+1` bookkeeping symbols (one `Phase`
plus `n` `Pauli1` letters). The tableau stores `n` such operators, so its
size is `n*(n+1) = O(n²)`.

**Time.** Each Clifford gate is local (acts on ≤ 2 qubits), so updating one
of the `n` Pauli generators requires only `O(n)` symbol-level work (walk the
length-`n` Pauli string). With `m` gates and `n` generators per gate, the
total cost is `m*n*n = O(mn²)`.

Below we just *encode* these as `def`s + `theorem`s — the user is expected
to prove the inequalities. -/

/-- Number of bookkeeping symbols in a single `PauliOp n`: one `Phase` + `n`
`Pauli1` letters. -/
def pauliOpSize (n : ℕ) : ℕ := n + 1

/-- Space cost of the tableau: `n` Pauli operators, each `pauliOpSize n` symbols. -/
def tableauSpace (n : ℕ) : ℕ := n * pauliOpSize n

/-- `tableauSpace n = O(n²)`: explicitly, `tableauSpace n ≤ (n+1)²`. -/
theorem tableauSpace_le (n : ℕ) : tableauSpace n ≤ (n + 1) ^ 2 := by
  -- TODO(you): unfold `tableauSpace`, `pauliOpSize`, and use `Nat.mul_le_mul` /
  -- `pow_two`. Should be `nlinarith` or `omega` after unfolding.
  sorry

/-- Symbol-level work to update one generator after one Clifford gate.
A Clifford gate touches a bounded number of qubits (1 or 2) but the
update conservatively walks the whole length-`n` Pauli string, so the
per-generator cost is `n`. -/
def gateUpdateCostPerGenerator (n : ℕ) : ℕ := n

/-- Cost of applying one Clifford gate to the whole tableau: `n` generators
× `gateUpdateCostPerGenerator n` = `n²`. -/
def gateUpdateCost (n : ℕ) : ℕ := n * gateUpdateCostPerGenerator n

/-- Total simulation cost: `m` gates × `n²` per gate. -/
def simulationCost (C : CliffordCircuit n) : ℕ := C.length * gateUpdateCost n

/-- `simulationCost C = O(m * n²)`: precisely, equality with `m * n²`. -/
theorem simulationCost_eq (C : CliffordCircuit n) :
    simulationCost C = C.length * n ^ 2 := by
  -- TODO(you): unfold the three definitions, then use `Nat.pow_succ` / `mul_assoc`.
  sorry

/-- The Gottesman–Knill complexity statement, packaged: for every circuit,
the classical simulation runs in `≤ m·n²` symbol updates using `≤ (n+1)²`
space. -/
theorem gottesman_knill_complexity (C : CliffordCircuit n) :
    simulationCost C = C.length * n ^ 2 ∧ tableauSpace n ≤ (n + 1) ^ 2 :=
  -- TODO(you): pair up `simulationCost_eq` and `tableauSpace_le`.
  ⟨by sorry, by sorry⟩

end GottesmanKnill
