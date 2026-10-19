import MagHK.MonopoleRealization

/-! The radial weak continuity equation follows from the actual magnetic form and its product rule. -/
noncomputable section
namespace MagHK.MonopoleStationarity
open MeasureTheory Set Filter
open MagHK.MonopoleRealization
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000

def radialFluxComponent (S : MagneticFormSystem) (ψ : S.domain) (i : Fin 2)
    (p : Chart × Chart) : ℝ :=
  (conj ((ψ : PairState) p) * S.pi i 0 ψ p).re

def multiplierFlux (S : MagneticFormSystem) (ψ : S.domain) (χ : ℝ → ℝ)
    (i : Fin 2) (p : Chart × Chart) : ℝ :=
  deriv χ (if i = 0 then p.1.1 else p.2.1) * radialFluxComponent S ψ i p

private theorem complex_integral_im {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).im = ∫ x, (f x).im ∂μ := (integral_im (𝕜 := ℂ) hf).symm

private theorem kinetic_im (z a : ℂ) (m d : ℝ) :
    (conj a * ((m : ℂ) * a - Complex.I * (d : ℂ) * z)).im =
      -d * (conj z * a).re := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

private theorem real_multiplier_im (z : ℂ) (m : ℝ) :
    (conj z * ((m : ℂ) * z)).im = 0 := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

private theorem real_potential_im (z : ℂ) (v m : ℝ) :
    ((v : ℂ) * conj z * ((m : ℂ) * z)).im = 0 := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem domain_antisymmetric_ae (S : MagneticFormSystem) (F : FermionSystem)
    (q : ℤ) (W : Chart × Chart → ℝ) (hS : MagneticFormFacts S F q W) (ψ : S.domain) :
    ∀ᵐ p ∂pairMeasure, (ψ : PairState) (p.2, p.1) = -(ψ : PairState) p := by
  have hm : (ψ : PairState) ∈ fermionSubspace := ((hS.domain_closure _).mp ψ.property).1
  have hz : swap (ψ : PairState) + (ψ : PairState) = 0 := hm
  have he : swap (ψ : PairState) = -(ψ : PairState) := eq_neg_of_add_eq_zero_left hz
  have hswap := Lp.coeFn_compMeasurePreserving (ψ : PairState) Measure.measurePreserving_swap
  change (fun p => swap (ψ : PairState) p) =ᵐ[pairMeasure]
    (fun p => (ψ : PairState) p.swap) at hswap
  rw [he] at hswap
  filter_upwards [hswap, Lp.coeFn_neg (ψ : PairState)] with p hp hn
  exact hp.symm.trans hn

/-- The imaginary eigenform equation, after a symmetric radial test multiplier. -/
theorem radial_weak_continuity_sum (S : MagneticFormSystem) (F : FermionSystem)
    (q : ℤ) (W : Chart × Chart → ℝ) (hS : MagneticFormFacts S F q W)
    (ψ : FermionState) (hψ : ψ ∈ F.domain) (E : ℝ)
    (heig : F.map ⟨ψ, hψ⟩ = E • ψ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : Function.support χ ⊆ Ioi 0) :
    let φ : S.domain := ⟨(ψ : PairState), hS.operator_domain ψ hψ⟩
    (∫ p, multiplierFlux S φ χ 0 p ∂pairMeasure) +
      (∫ p, multiplierFlux S φ χ 1 p ∂pairMeasure) = 0 := by
  let φ : S.domain := ⟨(ψ : PairState), hS.operator_domain ψ hψ⟩
  obtain ⟨ζ, hζ, hπζ⟩ := hS.symmetric_multiplier χ hχ hcχ hsχ φ
  have hk (i : Fin 2) (k : Fin 3) :
      (inner ℂ (S.pi i k φ) (S.pi i k ζ)).im =
        if k = 0 then -(∫ p, multiplierFlux S φ χ i p ∂pairMeasure) else 0 := by
    rw [L2.inner_def, complex_integral_im (L2.integrable_inner (𝕜 := ℂ) (S.pi i k φ) (S.pi i k ζ))]
    by_cases hk0 : k = 0
    · subst k
      rw [if_pos rfl, ← integral_neg]
      apply integral_congr_ae
      filter_upwards [hπζ i 0] with p hp
      simp only [RCLike.inner_apply', hp, if_pos rfl, ite_true, multiplierFlux, radialFluxComponent]
      simpa only [neg_mul] using kinetic_im ((φ : PairState) p) (S.pi i 0 φ p)
        (symmetricMultiplier χ p) (deriv χ (if i = 0 then p.1.1 else p.2.1))
    · rw [if_neg hk0]
      apply integral_eq_zero_of_ae
      filter_upwards [hπζ i k] with p hp
      simp only [RCLike.inner_apply', hp, if_neg hk0, sub_zero]
      exact real_multiplier_im _ _
  have hpoti : (∫ p, (fullPotential W p : ℂ) * conj ((φ : PairState) p) *
      (ζ : PairState) p ∂pairMeasure).im = 0 := by
    rw [complex_integral_im (hS.potential_integrable φ ζ)]
    apply integral_eq_zero_of_ae
    filter_upwards [hζ] with p hp
    rw [hp]
    exact real_potential_im _ _ _
  have hinneri : (inner ℂ (φ : PairState) (ζ : PairState)).im = 0 := by
    rw [L2.inner_def, complex_integral_im (L2.integrable_inner (𝕜 := ℂ) (φ : PairState) (ζ : PairState))]
    apply integral_eq_zero_of_ae
    filter_upwards [hζ] with p hp
    simp only [RCLike.inner_apply', hp]
    exact real_multiplier_im _ _
  have hf := congrArg Complex.im (hS.operator_form ψ hψ ζ)
  rw [heig] at hf
  have hrhs : (inner ℂ ((E • ψ : FermionState) : PairState) (ζ : PairState)).im = 0 := by
    change (inner ℂ (E • (φ : PairState)) (ζ : PairState)).im = 0
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left]
    simp [Complex.mul_im, hinneri]
  rw [hrhs] at hf
  change (formPairing S W φ ζ).im = 0 at hf
  simp only [formPairing, Fin.sum_univ_two, Fin.sum_univ_three, Complex.add_im] at hf
  rw [hk 0 0, hk 0 1, hk 0 2, hk 1 0, hk 1 1, hk 1 2, hpoti] at hf
  simp only [show (2 : Fin 3) ≠ 0 from by decide, ite_false, ite_true, add_zero] at hf
  norm_num at hf
  change (∫ p, multiplierFlux S φ χ 0 p ∂pairMeasure) +
    (∫ p, multiplierFlux S φ χ 1 p ∂pairMeasure) = 0
  linarith

theorem multiplierFlux_swap (S : MagneticFormSystem) (F : FermionSystem)
    (q : ℤ) (W : Chart × Chart → ℝ) (hS : MagneticFormFacts S F q W)
    (ψ : S.domain) (χ : ℝ → ℝ) :
    (fun p : Chart × Chart => multiplierFlux S ψ χ 1 p.swap) =ᵐ[pairMeasure]
      multiplierFlux S ψ χ 0 := by
  filter_upwards [domain_antisymmetric_ae S F q W hS ψ, hS.exchange ψ 1 0] with p hψ hπ
  change deriv χ p.1.1 * (conj ((ψ : PairState) (p.2, p.1)) *
    S.pi 1 0 ψ (p.2, p.1)).re =
    deriv χ p.1.1 * (conj ((ψ : PairState) p) * S.pi 0 0 ψ p).re
  rw [hψ, hπ, show (1 : Fin 2).rev = 0 from rfl]
  simp

theorem radial_weak_continuity (S : MagneticFormSystem) (F : FermionSystem)
    (q : ℤ) (W : Chart × Chart → ℝ) (hS : MagneticFormFacts S F q W)
    (ψ : FermionState) (hψ : ψ ∈ F.domain) (E : ℝ)
    (heig : F.map ⟨ψ, hψ⟩ = E • ψ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : Function.support χ ⊆ Ioi 0) :
    let φ : S.domain := ⟨(ψ : PairState), hS.operator_domain ψ hψ⟩
    ∫ p, deriv χ p.1.1 * radialFluxComponent S φ 0 p ∂pairMeasure = 0 := by
  let φ : S.domain := ⟨(ψ : PairState), hS.operator_domain ψ hψ⟩
  have hsum := radial_weak_continuity_sum S F q W hS ψ hψ E heig χ hχ hcχ hsχ
  change (∫ p, multiplierFlux S φ χ 0 p ∂pairMeasure) +
    (∫ p, multiplierFlux S φ χ 1 p ∂pairMeasure) = 0 at hsum
  have heq : (∫ p, multiplierFlux S φ χ 1 p ∂pairMeasure) =
      ∫ p, multiplierFlux S φ χ 0 p ∂pairMeasure := by
    unfold pairMeasure
    rw [← integral_prod_swap (multiplierFlux S φ χ 1)]
    exact integral_congr_ae (multiplierFlux_swap S F q W hS φ χ)
  rw [heq] at hsum
  change ∫ p, multiplierFlux S φ χ 0 p ∂pairMeasure = 0
  linarith

end MagHK.MonopoleStationarity
