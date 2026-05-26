import GottesmanKnill.Basic
import GottesmanKnill.PauliGroup
import GottesmanKnill.Clifford
import GottesmanKnill.QState
import GottesmanKnill.Stabilizer
import GottesmanKnill.StabilizerState
import GottesmanKnill.Heisenberg
import GottesmanKnill.MainTheorem

/-!
# Gottesman–Knill theorem in Lean

This library formalizes the proof of the Gottesman–Knill theorem following the LaTeX
notes in `GottsmanKnillLean/` (Ye, *Formalization of Gottesman–Knill theorem in Lean*).

The development is organized into one Lean file per LaTeX section:

* `GottesmanKnill.Basic`        — single-qubit Pauli operator, phase, basic gates
* `GottesmanKnill.PauliGroup`   — the n-qubit Pauli group `P_n` and its structure
* `GottesmanKnill.Clifford`     — the Clifford group `C_n = N(P_n) ∩ U_n`
* `GottesmanKnill.QState`       — abstract n-qubit state and stabilizer relation
* `GottesmanKnill.Stabilizer`   — the set `Stab(ψ)` and its Abelian-group structure
* `GottesmanKnill.StabilizerState` — stabilizer states and their `Stab ↔ ψ` bijection
* `GottesmanKnill.Heisenberg`   — evolution of `Stab(ψ)` under Clifford conjugation
* `GottesmanKnill.MainTheorem`  — the Gottesman–Knill theorem itself
-/
