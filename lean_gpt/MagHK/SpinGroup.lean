import MagHK.Symmetry
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! The literal two by two special unitary group. The sole background input
is its unitary diagonalization, a two-dimensional form of the spectral
 theorem. Triviality of characters is derived from explicit matrices. -/
noncomputable section
namespace MagHK.Spin
open scoped Matrix ComplexConjugate
abbrev Group := Matrix.specialUnitaryGroup (Fin 2) ℂ

def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp [phase, add_mul, Complex.exp_add]

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]
@[simp] theorem phase_conj (t : ℝ) : conj (phase t) = phase (-t) := by
  simp [phase, ← Complex.exp_conj]
@[simp] theorem phase_neg_mul (t : ℝ) : phase (-t) * phase t = 1 := by
  rw [← phase_add]
  simp
@[simp] theorem phase_mul_neg (t : ℝ) : phase t * phase (-t) = 1 := by
  rw [← phase_add]
  simp

def torusMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![phase t, 0; 0, phase (-t)]

def torus (t : ℝ) : Group := ⟨torusMatrix t, by
  constructor
  · change torusMatrix t ∈ Matrix.unitaryGroup (Fin 2) ℂ
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [torusMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
  · simp [torusMatrix, Matrix.det_fin_two]⟩

def flipMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

def flip : Group := ⟨flipMatrix, by
  constructor
  · change flipMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [flipMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
  · norm_num [flipMatrix, Matrix.det_fin_two]⟩

theorem torus_add (s t : ℝ) : torus (s + t) = torus s * torus t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torus, torusMatrix, Matrix.mul_apply, Fin.sum_univ_two, phase_add, neg_add, mul_comm]

theorem torus_zero : torus 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torus, torusMatrix]

theorem flip_torus (t : ℝ) : flip * torus t * flip⁻¹ = torus (-t) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flip, flipMatrix, torus, torusMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, ← Matrix.star_eq_inv, Matrix.star_eq_conjTranspose]

/-- Unitary diagonalization with determinant-one basis adjustment. This is
an operator-theory premise, with no eigenspace of the monopole Hamiltonian
or character conclusion in its statement. -/
def StandardUnitaryDiagonalization : Prop :=
  ∀ U : Group, ∃ Q : Group, ∃ t : ℝ, U = Q * torus t * Q⁻¹

theorem torus_character_trivial (χ : Group →* ℂˣ) (t : ℝ) : χ (torus t) = 1 := by
  have hc : χ (torus (t / 2)) = χ (torus (-(t / 2))) := by
    have h := congrArg χ (flip_torus (t / 2))
    simp only [map_mul, map_inv] at h
    rw [mul_right_comm, mul_inv_cancel, one_mul] at h
    exact h
  have hsum : torus t = torus (t / 2) * torus (t / 2) := by
    rw [← torus_add]
    congr 1
    ring
  rw [hsum, map_mul]
  calc
    _ = χ (torus (-(t / 2))) * χ (torus (t / 2)) := by rw [← hc]
    _ = 1 := by rw [← map_mul, ← torus_add, neg_add_cancel, torus_zero, map_one]

theorem character_trivial (L : StandardUnitaryDiagonalization)
    (χ : Group →* ℂˣ) (U : Group) : χ U = 1 := by
  obtain ⟨Q, t, rfl⟩ := L U
  simp [torus_character_trivial χ t]

theorem complex_character_trivial (L : StandardUnitaryDiagonalization)
    (χ : Group →* ℂ) (U : Group) : χ U = 1 := by
  have h := character_trivial L χ.toHomUnits U
  exact congrArg (fun z : ℂˣ => (z : ℂ)) h

/-- A nonzero vector on a rotation-invariant complex line is fixed. -/
theorem invariant_line_fixed {H : Type*} [AddCommGroup H] [Module ℂ H]
    (L : StandardUnitaryDiagonalization) (ρ : Group →* Module.End ℂ H)
    (ψ : H) (hψ : ψ ≠ 0) (hline : ∀ U, ∃ c : ℂ, ρ U ψ = c • ψ) :
    ∀ U, ρ U ψ = ψ := by
  intro U
  rw [MagHK.Symmetry.lineCharacter_action ρ ψ hψ hline U,
    complex_character_trivial L (MagHK.Symmetry.lineCharacter ρ ψ hψ hline) U, one_smul]

end MagHK.Spin
