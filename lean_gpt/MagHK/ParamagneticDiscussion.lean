import MagHK.CurrentCompletion
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The normalized paramagnetic-current identities in the discussion, for
the actual smooth noninteracting determinants. -/
noncomputable section
namespace MagHK.ParamagneticDiscussion
open MeasureTheory
open MagHK.CounterexamplePair
open scoped ComplexConjugate
abbrev Space := ℂ × ℝ

def paramagnetic (ψ : Space × Space → ℂ) (x d : Space) : ℝ :=
  2 * ∫ y, (conj (ψ (x, y)) * fderiv ℝ (fun z => ψ (z, y)) x d).im

theorem paramagnetic_of_zero (A : ℝ × ℝ → ℝ × ℝ) (ψ : Space × Space → ℂ)
    (x d : Space) (hj : current A ψ x d = 0) :
    paramagnetic ψ x d = -density ψ x * fieldPairing A x d := by
  change paramagnetic ψ x d + density ψ x * fieldPairing A x d = 0 at hj
  linarith

theorem normalized_of_zero (A : ℝ × ℝ → ℝ × ℝ) (ψ : Space × Space → ℂ)
    (x d : Space) (hρ : 0 < density ψ x) (hj : current A ψ x d = 0) :
    paramagnetic ψ x d / density ψ x = -fieldPairing A x d := by
  rw [paramagnetic_of_zero A ψ x d hj]
  field_simp

theorem conjugate_paramagnetic (ψ : Space × Space → ℂ) (x d : Space) :
    paramagnetic (fun p => conj (ψ p)) x d = -paramagnetic ψ x d := by
  simpa only [paramagnetic, MagHK.TimeReversal.paramagnetic, MagHK.OperatorTimeReversal.fderiv_conjugate,
    Complex.star_def, Pi.neg_apply] using congrFun
    (MagHK.TimeReversal.conjugate_paramagnetic volume
      (fun x y => ψ (x, y)) (fun x y => fderiv ℝ (fun z => ψ (z, y)) x d)) x

def normalizedPlanar (ψ : Space × Space → ℂ) (z : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (paramagnetic ψ (Complex.mk p.1 p.2, z) (1, 0) / density ψ (Complex.mk p.1 p.2, z),
   paramagnetic ψ (Complex.mk p.1 p.2, z) (Complex.I, 0) / density ψ (Complex.mk p.1 p.2, z))

theorem normalizedPlanar_eq (A : ℝ × ℝ → ℝ × ℝ) (ψ : Space × Space → ℂ)
    (hρ : ∀ x, 0 < density ψ x) (hj : ∀ x d, current A ψ x d = 0) (z : ℝ) :
    normalizedPlanar ψ z = -A := by
  funext p
  ext
  · simpa [normalizedPlanar, fieldPairing] using normalized_of_zero A ψ
      (Complex.mk p.1 p.2, z) (1, 0) (hρ _) (hj _ _)
  · simpa [normalizedPlanar, fieldPairing] using normalized_of_zero A ψ
      (Complex.mk p.1 p.2, z) (Complex.I, 0) (hρ _) (hj _ _)

theorem normalizedPlanar_curl (A : ℝ × ℝ → ℝ × ℝ) (ψ : Space × Space → ℂ)
    (hρ : ∀ x, 0 < density ψ x) (hj : ∀ x d, current A ψ x d = 0) (z : ℝ) :
    MagHK.Cartesian.planarCurl (normalizedPlanar ψ z) = -MagHK.Cartesian.planarCurl A := by
  rw [normalizedPlanar_eq A ψ hρ hj z, curl_neg]

theorem opposite_paramagnetic_differ (A : ℝ × ℝ → ℝ × ℝ) (ψ : Space × Space → ℂ)
    (hρ : ∀ x, 0 < density ψ x) (hj : ∀ x d, current A ψ x d = 0)
    (hA : MagHK.Cartesian.planarCurl A ≠ 0) :
    paramagnetic ψ ≠ paramagnetic (fun p => conj (ψ p)) := by
  intro he
  have hzero : A = 0 := by
    funext p
    have hx (d : Space) := congrFun (congrFun he (Complex.mk p.1 p.2, 0)) d
    have hz (d : Space) : fieldPairing A (Complex.mk p.1 p.2, 0) d = 0 := by
      have hxd := hx d
      rw [conjugate_paramagnetic, paramagnetic_of_zero A ψ _ _ (hj _ _)] at hxd
      have hp := hρ (Complex.mk p.1 p.2, 0)
      nlinarith [hxd]
    ext
    · simpa [fieldPairing] using hz (1, 0)
    · simpa [fieldPairing] using hz (Complex.I, 0)
  apply hA
  rw [hzero]
  funext p
  simp [MagHK.Cartesian.planarCurl]

theorem opposite_paramagnetic_differ_ae (A : ℝ × ℝ → ℝ × ℝ) (ψ : Space × Space → ℂ)
    (hAc : Continuous A) (hρ : ∀ x, 0 < density ψ x)
    (hj : ∀ x d, current A ψ x d = 0) (hA : MagHK.Cartesian.planarCurl A ≠ 0) :
    ¬ paramagnetic ψ =ᵐ[volume] paramagnetic (fun p => conj (ψ p)) := by
  intro he
  have ha : (fun x : Space => A (x.1.re, x.1.im)) =ᵐ[volume] 0 := by
    filter_upwards [he] with x hx
    have hz (d : Space) : fieldPairing A x d = 0 := by
      have hd := congrFun hx d
      rw [conjugate_paramagnetic, paramagnetic_of_zero A ψ x d (hj x d)] at hd
      nlinarith [hρ x]
    ext
    · simpa [fieldPairing] using hz (1, 0)
    · simpa [fieldPairing] using hz (Complex.I, 0)
  have hc : Continuous (fun x : Space => A (x.1.re, x.1.im)) :=
    hAc.comp ((Complex.continuous_re.comp continuous_fst).prodMk
      (Complex.continuous_im.comp continuous_fst))
  have heq := MeasureTheory.Measure.eq_of_ae_eq ha hc continuous_const
  have hzero : A = 0 := by
    funext p
    simpa using congrFun heq (Complex.mk p.1 p.2, 0)
  apply hA
  rw [hzero]
  funext p
  simp [MagHK.Cartesian.planarCurl]

theorem bounded_discussion (t c : ℝ) (ht : 0 ≤ t) (hc : 0 < c)
    (h : MagHK.Slater.OrthonormalPair volume
      (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c)) :
    (∀ z, normalizedPlanar (fun p => MagHK.ConcreteSlater.wave t c p.1 p.2) z =
      -MagHK.Cartesian.boundedVector t) ∧
    (∀ z, MagHK.Cartesian.planarCurl
      (normalizedPlanar (fun p => MagHK.ConcreteSlater.wave t c p.1 p.2) z) =
      -MagHK.Cartesian.planarCurl (MagHK.Cartesian.boundedVector t)) ∧
    (0 < t → paramagnetic (fun p => MagHK.ConcreteSlater.wave t c p.1 p.2) ≠
      paramagnetic (fun p => conj (MagHK.ConcreteSlater.wave t c p.1 p.2))) := by
  let ψ : Space × Space → ℂ := fun p => MagHK.ConcreteSlater.wave t c p.1 p.2
  have hρ (x : Space) : 0 < density ψ x := by
    change 0 < 2 * ∫ y, Complex.normSq (MagHK.ConcreteSlater.wave t c x y)
    rw [MagHK.ConcreteSlater.wave_density_marginal t c h x]
    exact MagHK.ConcreteSlater.density_pos t c ht hc x
  have hj (x d : Space) : current (MagHK.Cartesian.boundedVector t) ψ x d = 0 := by
    rw [bounded_current_eq]
    exact MagHK.CurrentCompletion.Bounded.physicalCurrent_zero t c ht h x d
  exact ⟨normalizedPlanar_eq _ ψ hρ hj, normalizedPlanar_curl _ ψ hρ hj,
    fun ht' => opposite_paramagnetic_differ _ ψ hρ hj (MagHK.Cartesian.bounded_curl_nonzero t ht')⟩

theorem gaussian_discussion (t c : ℝ) (ht : 0 ≤ t) (hc : 0 < c)
    (h : MagHK.Slater.OrthonormalPair volume
      (MagHK.GaussianOrbitals.orbitalZero t c) (MagHK.GaussianOrbitals.orbitalMinus t c)) :
    (∀ z, normalizedPlanar (fun p => MagHK.GaussianSlater.wave t c p.1 p.2) z =
      -MagHK.Cartesian.gaussianVector t) ∧
    (∀ z, MagHK.Cartesian.planarCurl
      (normalizedPlanar (fun p => MagHK.GaussianSlater.wave t c p.1 p.2) z) =
      -MagHK.Cartesian.planarCurl (MagHK.Cartesian.gaussianVector t)) ∧
    (0 < t → paramagnetic (fun p => MagHK.GaussianSlater.wave t c p.1 p.2) ≠
      paramagnetic (fun p => conj (MagHK.GaussianSlater.wave t c p.1 p.2))) := by
  let ψ : Space × Space → ℂ := fun p => MagHK.GaussianSlater.wave t c p.1 p.2
  have hρ (x : Space) : 0 < density ψ x := by
    change 0 < 2 * ∫ y, Complex.normSq (MagHK.GaussianSlater.wave t c x y)
    rw [MagHK.GaussianSlater.wave_density_marginal t c h x]
    exact MagHK.GaussianSlater.density_pos t c ht hc x
  have hj (x d : Space) : current (MagHK.Cartesian.gaussianVector t) ψ x d = 0 := by
    rw [gaussian_current_eq]
    exact MagHK.CurrentCompletion.Gaussian.physicalCurrent_zero t c ht h x d
  exact ⟨normalizedPlanar_eq _ ψ hρ hj, normalizedPlanar_curl _ ψ hρ hj,
    fun ht' => opposite_paramagnetic_differ _ ψ hρ hj (MagHK.Cartesian.gaussian_curl_nonzero t ht')⟩

theorem bounded_paramagnetic_differ_ae (t c : ℝ) (ht : 0 < t) (hc : 0 < c)
    (h : MagHK.Slater.OrthonormalPair volume
      (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c)) :
    ¬ paramagnetic (fun p => MagHK.ConcreteSlater.wave t c p.1 p.2) =ᵐ[volume]
      paramagnetic (fun p => conj (MagHK.ConcreteSlater.wave t c p.1 p.2)) := by
  apply opposite_paramagnetic_differ_ae (MagHK.Cartesian.boundedVector t) _
    (MagHK.Cartesian.boundedVector_contDiff t ht.le).continuous
  · intro x
    change 0 < 2 * ∫ y, Complex.normSq (MagHK.ConcreteSlater.wave t c x y)
    rw [MagHK.ConcreteSlater.wave_density_marginal t c h x]
    exact MagHK.ConcreteSlater.density_pos t c ht.le hc x
  · intro x d
    rw [bounded_current_eq]
    exact MagHK.CurrentCompletion.Bounded.physicalCurrent_zero t c ht.le h x d
  · exact MagHK.Cartesian.bounded_curl_nonzero t ht

theorem gaussian_paramagnetic_differ_ae (t c : ℝ) (ht : 0 < t) (hc : 0 < c)
    (h : MagHK.Slater.OrthonormalPair volume
      (MagHK.GaussianOrbitals.orbitalZero t c) (MagHK.GaussianOrbitals.orbitalMinus t c)) :
    ¬ paramagnetic (fun p => MagHK.GaussianSlater.wave t c p.1 p.2) =ᵐ[volume]
      paramagnetic (fun p => conj (MagHK.GaussianSlater.wave t c p.1 p.2)) := by
  apply opposite_paramagnetic_differ_ae (MagHK.Cartesian.gaussianVector t) _
    (MagHK.Cartesian.gaussianVector_contDiff t ht.le).continuous
  · intro x
    change 0 < 2 * ∫ y, Complex.normSq (MagHK.GaussianSlater.wave t c x y)
    rw [MagHK.GaussianSlater.wave_density_marginal t c h x]
    exact MagHK.GaussianSlater.density_pos t c ht.le hc x
  · intro x d
    rw [gaussian_current_eq]
    exact MagHK.CurrentCompletion.Gaussian.physicalCurrent_zero t c ht.le h x d
  · exact MagHK.Cartesian.gaussian_curl_nonzero t ht

end MagHK.ParamagneticDiscussion
