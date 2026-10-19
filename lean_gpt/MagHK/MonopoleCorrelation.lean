import MagHK.MonopoleTensorDomain
import MagHK.MonopoleObstruction
import MagHK.MonopoleExpectation
import MagHK.SeparatedDifferential

/-! An actual interacting eigenstate cannot have the separated common-radial
angular determinant. The operator image is reduced using general tensor and
Coulomb domain theorems, then the literal angular obstruction is applied. -/
noncomputable section
namespace MagHK.MonopoleSeparation
open MeasureTheory Set
open MagHK.MonopoleRealization MagHK.MonopoleTrial MagHK.MonopoleTensorDomain
open MagHK.MonopoleExpectation MagHK.MonopoleObstruction

/-- No a.e. separated common-radial product can be a nonzero eigenstate. -/
theorem no_separated_eigenstate
    (domains : StandardCoulombOperatorLibrary) (tensor : StandardSeparatedDomainLibrary)
    (F₀ F : FermionSystem) (hF₀ : FermionFacts F₀ 1 0) (hF : FermionFacts F 1 coulomb)
    (E : ℝ) (ψ : FermionState) (hψ : OperatorModel.Eigen F E ψ)
    (f : ℝ → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hn : (∫ r, Complex.normSq (f r) ∂radialVolume) = 1)
    (hrep : ∀ᵐ p ∂pairMeasure, (ψ : PairState) p = c * separatedWave f p) : False := by
  obtain ⟨hD, _, hE⟩ := hψ
  obtain ⟨hD₀, hsum⟩ := domains 1 F₀ F hF₀ hF ψ hD
  obtain ⟨h, himage⟩ := tensor 1 F₀ hF₀ (1 / 2) Yplus Yminus
    (by simpa using plus_angular_solution) (by simpa using minus_angular_solution)
      doublet_orthonormal f c hn ψ hD₀ hrep
  have heq : ∀ᵐ p ∂pairMeasure,
      (h p.1.1 * f p.2.1 + f p.1.1 * h p.2.1 +
        ((coulomb p : ℂ) - E) * (f p.1.1 * f p.2.1)) * angularDet p.1.2 p.2.2 = 0 := by
    have hs : ∀ᵐ p ∂pairMeasure,
        ((F.map ⟨ψ, hD⟩ : FermionState) : PairState) p = (E : ℂ) * (ψ : PairState) p := by
      rw [hE]
      exact (Lp.coeFn_smul E (ψ : PairState)).mono (fun _ hx => by simpa using hx)
    filter_upwards [hsum, himage, hrep, hs] with p hsum himage hrep hs
    have he : c * ((h p.1.1 * f p.2.1 + f p.1.1 * h p.2.1 +
        ((coulomb p : ℂ) - E) * (f p.1.1 * f p.2.1)) * angularDet p.1.2 p.2.2) = 0 := by
      rw [himage, hrep, hs] at hsum
      rw [hrep] at hsum
      dsimp only [angularWedge, angularDet, separatedWave] at hsum ⊢
      linear_combination -hsum
    exact (mul_eq_zero.mp he).resolve_left hc
  have htrial : ∀ᵐ x ∂trialMeasure,
      (h x.1.1 * f x.1.2 + f x.1.1 * h x.1.2 +
        (((1 / pairDistance x.1.1 x.1.2 x.2 : ℝ) : ℂ) - E) * (f x.1.1 * f x.1.2)) *
          angularDet x.2.1 x.2.2 = 0 := by
    have hm := (MeasurePreserving.symm regroup regroup_measurePreserving).quasiMeasurePreserving.ae heq
    exact hm
  have hprod : ∀ᵐ s ∂radialVolume, ∀ᵐ t ∂radialVolume, f s * f t = 0 := by
    have hiter := Measure.ae_ae_of_ae_prod (Measure.ae_ae_of_ae_prod htrial)
    filter_upwards [hiter, radialVolume_ae] with s hs hspos
    filter_upwards [hs, radialVolume_ae] with t ht htpos
    by_contra hne
    apply no_ae_pair_coulomb_multiple s t (f s * f t)
      (h s * f t + f s * h t - (E : ℂ) * (f s * f t)) hspos htpos hne
    filter_upwards [ht] with p hp
    convert hp using 1
    ring
  have hf : ∀ᵐ s ∂radialVolume, f s = 0 := by
    by_contra hnonzero
    apply hnonzero
    filter_upwards [hprod] with s hs
    by_contra hsne
    apply hnonzero
    filter_upwards [hs] with t ht
    exact (mul_eq_zero.mp ht).resolve_left hsne
  have hi : (∫ r, Complex.normSq (f r) ∂radialVolume) = 0 := by
    calc
      _ = ∫ _r, (0 : ℝ) ∂radialVolume := by
        apply integral_congr_ae
        filter_upwards [hf] with r hr
        simp [hr]
      _ = 0 := integral_zero _ _
  linarith

theorem coefficient_nonzero (ψ : FermionState) (hψ : ψ ≠ 0)
    (f : ℝ → ℂ) (c : ℂ)
    (hrep : ∀ᵐ p ∂pairMeasure, (ψ : PairState) p = c * separatedWave f p) : c ≠ 0 := by
  intro hc
  apply hψ
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hrep, Lp.coeFn_zero ℂ 2 pairMeasure] with p hp hz
  change (ψ : PairState) p = (0 : PairState) p
  rw [hz]
  simpa [hc] using hp

end MagHK.MonopoleSeparation
