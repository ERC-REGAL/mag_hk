import MagHK.GaussianAxial
import MagHK.GaussianPlanar
import MagHK.GaussianSlater
import MagHK.FermionRealization

/-! The Gaussian construction in the actual three-dimensional and fermionic
Hilbert spaces. All selected-orbital and determinant inputs are proved.
The only external inputs are the universal operator libraries. -/
noncomputable section
namespace MagHK.GaussianFermion
open MeasureTheory Set
open MagHK.Noninteracting MagHK.RadialEndpoints MagHK.Cartesian
open MagHK.GaussianIntegrals MagHK.GaussianDomains MagHK.GaussianRealization
open MagHK.TensorRealization
open scoped ContDiff ComplexConjugate

private theorem normalization_ne_zero : (GaussianOrbitals.normalization : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt GaussianSlater.normalization_pos)

theorem gaussian_zero_eigenfunction (t c : ℝ) (ht : 0 < t) (hc : 0 < c)
    (P : PlanarSpectralLibrary.System) (Z : AxialRealization.System) (T : System)
    (hP : PlanarSpectralLibrary.Facts P (gaussianA t) (scalar t) (gaussianU t)
      (gaussianVector t) (gaussianScalar t))
    (hz : AxialRealization.Eigen Z 0 (GaussianAxial.chiState c hc))
    (hT : Facts T P Z (gaussianVector t) (gaussianScalar t) (GaussianAxial.potential c)) :
    EigenFunction T 0 (GaussianOrbitals.orbitalZero t c) := by
  have hs := gaussian_zero_solution t ht
  obtain ⟨hd, he⟩ := hP.radial_facts.regular_solution
    (gaussian_coefficients t ht) 0 0 _ _ hs
  have hei : RadialRealization.Eigen P.radial 0 0 := ⟨_, hd, hs.nonzero, he⟩
  have hout := hT.separated_eigenfunction 0 0 0 (gaussianF t) (axialChi c)
    (GaussianRealization.zeroState t ht.le) (GaussianAxial.chiState c hc)
    (GaussianOrbitals.orbitalZero t c) (GaussianOrbitals.normalization : ℂ)
    hei hz hs.represented ⟨hd, hs.nonzero, he⟩
    (GaussianAxial.chi_memLp c hc).coeFn_toLp ?_ normalization_ne_zero
  · simpa only [add_zero] using hout
  · intro r θ z hr
    rw [GaussianOrbitals.orbitalZero_pullback t c (r, θ, z) hr.le]
    simp [GaussianOrbitals.cylindricalZero]

theorem gaussian_minus_eigenfunction (t c : ℝ) (ht : 0 < t) (hc : 0 < c)
    (P : PlanarSpectralLibrary.System) (Z : AxialRealization.System) (T : System)
    (hP : PlanarSpectralLibrary.Facts P (gaussianA t) (scalar t) (gaussianU t)
      (gaussianVector t) (gaussianScalar t))
    (hz : AxialRealization.Eigen Z 0 (GaussianAxial.chiState c hc))
    (hT : Facts T P Z (gaussianVector t) (gaussianScalar t) (GaussianAxial.potential c)) :
    EigenFunction T 2 (GaussianOrbitals.orbitalMinus t c) := by
  have hs := gaussian_minus_solution t ht
  obtain ⟨hd, he⟩ := hP.radial_facts.regular_solution
    (gaussian_coefficients t ht) (-1) 2 _ _ hs
  have hei : RadialRealization.Eigen P.radial (-1) 2 := ⟨_, hd, hs.nonzero, he⟩
  have hk : (GaussianOrbitals.normalization : ℂ) * (Real.sqrt t : ℂ) ≠ 0 :=
    mul_ne_zero normalization_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr ht))
  have hout := hT.separated_eigenfunction (-1) 2 0 (SecondOrbital.gaussianProduct t) (axialChi c)
    (GaussianRealization.minusState t ht.le) (GaussianAxial.chiState c hc)
    (GaussianOrbitals.orbitalMinus t c)
    ((GaussianOrbitals.normalization : ℂ) * (Real.sqrt t : ℂ))
    hei hz hs.represented ⟨hd, hs.nonzero, he⟩
    (GaussianAxial.chi_memLp c hc).coeFn_toLp ?_ hk
  · simpa only [add_zero] using hout
  · intro r θ z hr
    rw [GaussianOrbitals.orbitalMinus_pullback t c (r, θ, z) hr.le]
    simp only [GaussianOrbitals.cylindricalMinus, GaussianOrbitals.radialSecond,
      CylindricalOrbitals.phase_eq_negative_exp, SecondOrbital.gaussianProduct,
      Complex.ofReal_mul, Int.cast_neg, Int.cast_one, neg_one_mul, Complex.ofReal_neg]
    simp only [neg_mul, mul_neg, mul_comm Complex.I (θ : ℂ)]
    ring

theorem gaussian_density (t c : ℝ) (ht : 0 ≤ t) (x : Space) :
    GaussianSlater.density t c x =
      (2 / Real.pi) * Real.sqrt (c / Real.pi) * Real.exp (-‖x.1‖ ^ 2 - c * x.2 ^ 2) := by
  have hD : 1 + t * ‖x.1‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hN : GaussianOrbitals.normalization ^ 2 = 2 / Real.pi :=
    Real.sq_sqrt (by positivity)
  calc
    GaussianSlater.density t c x = GaussianOrbitals.normalization ^ 2 *
        (1 + t * ‖x.1‖ ^ 2) * gaussianF t ‖x.1‖ ^ 2 * axialChi c x.2 ^ 2 := by
      rw [GaussianSlater.density_formula]
      unfold GaussianSlater.amplitudeZero GaussianSlater.amplitudeMinus
      simp only [mul_pow, Real.sq_sqrt ht]
      ring
    _ = (2 / Real.pi) * Real.sqrt (c / Real.pi) *
        (Real.exp (-‖x.1‖ ^ 2) * Real.exp (-c * x.2 ^ 2)) := by
      rw [hN, gaussianF_squared t ‖x.1‖ ht, axialChi_squared]
      field_simp
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem gaussian_ground_state
    (planar : PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : GaussianAxial.StandardOscillatorLibrary)
    (tensor : StandardTensorLibrary) (fermion : FermionRealization.StandardFermionLibrary)
    (c : ℝ) (hc : 1 < c) :
    ∃ t : ℝ, 0 < t ∧ ∃ T : System, ∃ F : FermionRealization.System,
      FermionRealization.OneBodyRealization T (gaussianVector t) (gaussianScalar t)
        (GaussianAxial.potential c) ∧
      (∀ E, E ∈ OperatorModel.spectrum T ∧ E ≤ 2 ↔ E = 0 ∨ E = 2) ∧
      OperatorModel.multiplicity T 0 = 1 ∧ OperatorModel.multiplicity T 2 = 1 ∧
      FermionRealization.Facts F (gaussianVector t) (gaussianScalar t) (GaussianAxial.potential c) ∧
      FermionRealization.GroundState F 2 (fun p => GaussianSlater.wave t c p.1 p.2) ∧
      (∫ p : Space × Space, Complex.normSq (GaussianSlater.wave t c p.1 p.2)) = 1 ∧
      (∀ x, 2 * ∫ y, Complex.normSq (GaussianSlater.wave t c x y) =
        (2 / Real.pi) * Real.sqrt (c / Real.pi) * Real.exp (-‖x.1‖ ^ 2 - c * x.2 ^ 2)) ∧
      (∀ᵐ x : Space, ∀ d : Space, GaussianSlater.physicalCurrent t c x d = 0) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨t, ht, hn0, hn1⟩ := exists_gaussian_equal_norms
  obtain ⟨P, hP, hlevels, hp0, hp2, hpgap⟩ :=
    GaussianPlanar.gaussian_planar_realization planar t ht
  obtain ⟨Z, hZ, hz, hz0, hzm, hzgap⟩ := GaussianAxial.gaussian_axial_realization axial c hc0
  have hpnon : ∀ E ∈ P.spectrum, 0 ≤ E := by
    intro E hE
    by_cases he : E ≤ 2
    · rcases (hlevels E).mp ⟨hE, he⟩ with rfl | rfl <;> norm_num
    · linarith
  obtain ⟨T, hT⟩ := tensor P Z _ _ _ _ _ _ _
    (GaussianPlanar.gaussian_planar_coefficients t ht.le) (GaussianAxial.potential_smooth c)
    hP hZ hpnon hZ.nonnegative
  have h1 : FermionRealization.OneBodyRealization T (gaussianVector t) (gaussianScalar t)
      (GaussianAxial.potential c) := ⟨hT.selfadjoint, hT.test_action, hT.weak_equation⟩
  obtain ⟨hle, hm0, hm2, htg⟩ := tensor_levels T P Z _ _ _ hT 2 (2 * c)
    (by norm_num) (by linarith) hlevels hp0 hp2 hpgap hz0 hzm hzgap
  have hzero := gaussian_zero_eigenfunction t c ht hc0 P Z T hP hz hT
  have hminus := gaussian_minus_eigenfunction t c ht hc0 P Z T hP hz hT
  have ho := GaussianOrbitals.gaussian_orthonormal t c ht hc0 hn0 hn1
  obtain ⟨F, hF, hg⟩ := fermion T _ _ _ h1 0 2 _ _ (by norm_num)
    hle hm0 hm2 htg hzero hminus ho
  refine ⟨t, ht, T, F, h1, hle, hm0, hm2, hF, ?_,
    GaussianSlater.wave_normalized t c ht.le ho, ?_,
    GaussianSlater.physicalCurrent_zero_ae t c ht.le ho⟩
  · simpa only [zero_add] using! hg
  · intro x
    rw [GaussianSlater.wave_density_marginal t c ho x, gaussian_density t c ht.le x]

theorem gaussian_example
    (planar : PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : GaussianAxial.StandardOscillatorLibrary)
    (tensor : StandardTensorLibrary) (fermion : FermionRealization.StandardFermionLibrary)
    (c : ℝ) (hc : 1 < c) :
    ∃ t : ℝ, 0 < t ∧
      ContDiff ℝ ∞ (ConstructionData.gaussian3Vector t) ∧
      ContDiff ℝ ∞ (ConstructionData.gaussian3Scalar t c) ∧
      (∃ C : ℝ, ∀ p, ‖ConstructionData.gaussian3Vector t p‖ ≤ C) ∧
      planarCurl (gaussianVector t) ≠ 0 ∧
      ∃ F : FermionRealization.System,
      FermionRealization.Facts F (gaussianVector t) (gaussianScalar t) (GaussianAxial.potential c) ∧
      FermionRealization.GroundState F 2 (fun p => GaussianSlater.wave t c p.1 p.2) ∧
      (∫ p : Space × Space, Complex.normSq (GaussianSlater.wave t c p.1 p.2)) = 1 ∧
      (∀ x, 2 * ∫ y, Complex.normSq (GaussianSlater.wave t c x y) =
        (2 / Real.pi) * Real.sqrt (c / Real.pi) * Real.exp (-‖x.1‖ ^ 2 - c * x.2 ^ 2)) ∧
      (∀ᵐ x : Space, ∀ d : Space, GaussianSlater.physicalCurrent t c x d = 0) := by
  obtain ⟨t, ht, T, F, _, _, _, _, hF, hg, hn, hρ, hj⟩ :=
    gaussian_ground_state planar axial tensor fermion c hc
  exact ⟨t, ht, ConstructionData.gaussian3Vector_smooth t ht.le,
    ConstructionData.gaussian3Scalar_smooth t c ht.le,
    ⟨t + 1, ConstructionData.gaussian3Vector_bound t ht.le⟩,
    gaussian_curl_nonzero t ht, F, hF, hg, hn, hρ, hj⟩

end MagHK.GaussianFermion
