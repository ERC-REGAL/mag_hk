import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
Local reconstruction and continuation for Proposition `prop:one-particle`.

`scalar_reconstruction` is a division-free local jet identity for a complex
magnetic eigenfunction. It avoids the extra C² regularity that the draft
explicitly does not assume. Weak derivatives can supply the jets almost
everywhere after the allowed elliptic-regularity step.

`global_uniqueness_from_local_reconstruction` performs the full-measure to
everywhere step. Its reconstruction hypotheses must be instantiated from
weak calculus. These are visible parameters, not axioms.
-/

namespace MagHK.OneParticle

open MeasureTheory
open scoped BigOperators

theorem complex_jet_identity (u v du dv : ℝ) :
    (u * du + v * dv)^2 + (u * dv - v * du)^2 =
      (u^2 + v^2) * (du^2 + dv^2) := by ring

/-- Real and imaginary parts of the magnetic Schrödinger equation imply
the density reconstruction identity in each finite dimension. -/
theorem scalar_reconstruction {n : ℕ}
    (u v lapU lapV divA V E : ℝ) (du dv A : Fin n → ℝ)
    (hreal : -lapU + 2 * ∑ i, A i * dv i + divA * v +
      ((∑ i, (A i)^2) + V - E) * u = 0)
    (himag : -lapV - 2 * ∑ i, A i * du i - divA * u +
      ((∑ i, (A i)^2) + V - E) * v = 0) :
    (u^2 + v^2)^2 * (V - E) =
      (u^2 + v^2) *
        ((∑ i, ((du i)^2 + (dv i)^2)) + u * lapU + v * lapV) -
      (∑ i, (u * du i + v * dv i)^2) -
      (∑ i, (u * dv i - v * du i + (u^2 + v^2) * A i)^2) := by
  have hi (i : Fin n) :
      (u * du i + v * dv i)^2 +
        (u * dv i - v * du i + (u^2 + v^2) * A i)^2 =
      (u^2 + v^2) * ((du i)^2 + (dv i)^2) +
      2 * (u^2 + v^2) * (u * (A i * dv i) - v * (A i * du i)) +
      (u^2 + v^2)^2 * (A i)^2 := by ring
  have hs := Finset.sum_congr rfl (fun (i : Fin n) (_ : i ∈ Finset.univ) => hi i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at hs
  have hSch : u * lapU + v * lapV =
      2 * (u * (∑ i, A i * dv i) - v * (∑ i, A i * du i)) +
      ((∑ i, (A i)^2) + V - E) * (u^2 + v^2) := by
    linear_combination -u * hreal - v * himag
  simp only [Finset.sum_add_distrib]
  linear_combination hs - (u^2 + v^2) * hSch

/-- Antisymmetric derivative of the local phase velocity is zero.
Mixed second derivatives cancel before this identity is applied. -/
theorem phase_curl_numerator (u v ui vi uj vj : ℝ) :
    2 * (ui * vj - uj * vi) * (u^2 + v^2) -
      ((u * vj - v * uj) * (2 * (u * ui + v * vi)) -
       (u * vi - v * ui) * (2 * (u * uj + v * vj))) = 0 := by ring

/-- The quotient-rule expressions for the two cross derivatives differ
by precisely the corresponding cross derivatives of the vector potential.
The mixed second derivative jets `uij` and `vij` are shared. -/
theorem curl_reconstruction (u v ui vi uj vj uij vij Aij Aji : ℝ)
    (hρ : u^2 + v^2 ≠ 0) :
    (((ui * vj + u * vij - vi * uj - v * uij) * (u^2 + v^2) -
      (u * vj - v * uj) * (2 * (u * ui + v * vi))) / (u^2 + v^2)^2 + Aij) -
    (((uj * vi + u * vij - vj * ui - v * uij) * (u^2 + v^2) -
      (u * vi - v * ui) * (2 * (u * uj + v * vj))) / (u^2 + v^2)^2 + Aji) =
    Aij - Aji := by
  field_simp
  ring

theorem reconstruct_potential (ρ lapρ gradρsq jsq V E : ℝ)
    (hρ : ρ ≠ 0)
    (h : ρ^2 * (V - E) = ρ * lapρ / 2 - gradρsq / 4 - jsq) :
    V - E = lapρ / (2 * ρ) - gradρsq / (4 * ρ^2) - jsq / ρ^2 := by
  field_simp
  nlinarith [h]

theorem equal_reconstructed_potentials (ρ L G J V₁ V₂ E₁ E₂ : ℝ)
    (hρ : ρ ≠ 0)
    (h₁ : ρ^2 * (V₁ - E₁) = ρ * L / 2 - G / 4 - J)
    (h₂ : ρ^2 * (V₂ - E₂) = ρ * L / 2 - G / 4 - J) :
    V₁ - V₂ = E₁ - E₂ := by
  have hp : ρ^2 ≠ 0 := pow_ne_zero _ hρ
  have h : V₁ - E₁ = V₂ - E₂ := mul_left_cancel₀ hp (h₁.trans h₂.symm)
  linarith

/-- This is the global continuation step, using a measure with full support.
For the manuscript it is Lebesgue measure on ℝ³. -/
theorem global_uniqueness_from_local_reconstruction
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure]
    (ρ V₁ V₂ B₁ B₂ L G J : X → ℝ) (E₁ E₂ : ℝ)
    (hρ : ∀ᵐ x ∂μ, ρ x ≠ 0)
    (hV₁ : Continuous V₁) (hV₂ : Continuous V₂)
    (hB₁ : Continuous B₁) (hB₂ : Continuous B₂)
    (hlocal₁ : ∀ᵐ x ∂μ, ρ x ≠ 0 →
      ρ x ^ 2 * (V₁ x - E₁) = ρ x * L x / 2 - G x / 4 - J x)
    (hlocal₂ : ∀ᵐ x ∂μ, ρ x ≠ 0 →
      ρ x ^ 2 * (V₂ x - E₂) = ρ x * L x / 2 - G x / 4 - J x)
    (hcurl : ∀ᵐ x ∂μ, ρ x ≠ 0 → B₁ x = B₂ x) :
    (∀ x, V₁ x - V₂ x = E₁ - E₂) ∧ B₁ = B₂ := by
  have hv : (fun x => V₁ x - V₂ x) =ᵐ[μ] (fun _ => E₁ - E₂) := by
    filter_upwards [hρ, hlocal₁, hlocal₂] with x hx h₁ h₂
    exact equal_reconstructed_potentials _ _ _ _ _ _ _ _ hx (h₁ hx) (h₂ hx)
  have hV := MeasureTheory.Measure.eq_of_ae_eq hv (hV₁.sub hV₂) continuous_const
  refine ⟨fun x => congrFun hV x, ?_⟩
  apply MeasureTheory.Measure.eq_of_ae_eq (μ := μ) _ hB₁ hB₂
  filter_upwards [hρ, hcurl] with x hx hb
  exact hb hx

end MagHK.OneParticle
