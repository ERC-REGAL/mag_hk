import MagHK.OperatorTimeReversal
import MagHK.Curvature
import MagHK.GaussianFermion
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! Literal density/current reversal and a differential gauge obstruction for
both smooth constructions. The bounded opposite-potential ground-state pair is
assembled from the actual operator conjugation, not from a chosen-example
spectral assumption. -/
noncomputable section
namespace MagHK.CounterexamplePair
open MeasureTheory
open MagHK.TensorRealization MagHK.FermionRealization MagHK.OperatorTimeReversal
open scoped ComplexConjugate ContDiff

def density (ψ : Space × Space → ℂ) (x : Space) : ℝ :=
  2 * ∫ y, Complex.normSq (ψ (x, y))

def fieldPairing (A : ℝ × ℝ → ℝ × ℝ) (x d : Space) : ℝ :=
  (A (x.1.re, x.1.im)).1 * d.1.re + (A (x.1.re, x.1.im)).2 * d.1.im

def current (A : ℝ × ℝ → ℝ × ℝ) (ψ : Space × Space → ℂ) (x d : Space) : ℝ :=
  2 * (∫ y, (conj (ψ (x, y)) * fderiv ℝ (fun z => ψ (z, y)) x d).im) +
    density ψ x * fieldPairing A x d

theorem density_conjugate (ψ : Space × Space → ℂ) (x : Space) :
    density (fun p => conj (ψ p)) x = density ψ x := by simp [density]

theorem current_conjugate (A : ℝ × ℝ → ℝ × ℝ) (ψ : Space × Space → ℂ) (x d : Space) :
    current (-A) (fun p => conj (ψ p)) x d = -current A ψ x d := by
  have h := congrFun (MagHK.TimeReversal.conjugate_current volume
    (fun x y => ψ (x, y)) (fun x y => fderiv ℝ (fun z => ψ (z, y)) x d)
    (fun x => fieldPairing A x d)) x
  simpa only [current, density, MagHK.TimeReversal.current, MagHK.TimeReversal.paramagnetic,
    MagHK.TimeReversal.density, fderiv_conjugate, Complex.star_def, Pi.neg_apply,
    fieldPairing, Prod.fst_neg, Prod.snd_neg, neg_mul, neg_add] using h

theorem normalization_conjugate (ψ : Space × Space → ℂ) :
    (∫ p, Complex.normSq (conj (ψ p))) = ∫ p, Complex.normSq (ψ p) := by simp

theorem bounded_current_eq (t c : ℝ) (x d : Space) :
    current (Cartesian.boundedVector t) (fun p => ConcreteSlater.wave t c p.1 p.2) x d =
      ConcreteSlater.physicalCurrent t c x d := by
  simp only [current, density, fieldPairing, ConcreteSlater.physicalCurrent,
    ConcreteSlater.fieldPairing, ConcreteSlater.realCoordinates,
    ConstructionData.bounded3Vector, Complex.star_def, zero_mul, add_zero]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem mixed_derivatives (f : X → ℝ) (hf : ContDiff ℝ 2 f) (x v w : X) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v =
      fderiv ℝ (fun y => fderiv ℝ f y v) x w := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [fderiv_clm_apply (hd x) (differentiableAt_const w),
    fderiv_clm_apply (hd x) (differentiableAt_const v)]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using
    (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num) v w

def planarGradient (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (fderiv ℝ f p (1, 0), fderiv ℝ f p (0, 1))

theorem curl_gradient (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ 2 f) :
    Cartesian.planarCurl (planarGradient f) = 0 := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  funext p
  have h1 := ((hd p).clm_apply (differentiableAt_const (0, 1))).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  have h2 := ((hd p).clm_apply (differentiableAt_const (1, 0))).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  change Cartesian.planarCurl (planarGradient f) p = 0
  have he1 : deriv (fun x => fderiv ℝ f (x, p.2) (0, 1)) p.1 =
      fderiv ℝ (fun y => fderiv ℝ f y (0, 1)) p (1, 0) := by
    simpa only [Function.comp_def, id_eq] using! h1.deriv
  have he2 : deriv (fun y => fderiv ℝ f (p.1, y) (1, 0)) p.2 =
      fderiv ℝ (fun y => fderiv ℝ f y (1, 0)) p (0, 1) := by
    simpa only [Function.comp_def, id_eq] using! h2.deriv
  change deriv (fun x => fderiv ℝ f (x, p.2) (0, 1)) p.1 -
    deriv (fun y => fderiv ℝ f (p.1, y) (1, 0)) p.2 = 0
  rw [he1, he2, mixed_derivatives f hf p (1, 0) (0, 1), sub_self]

theorem curl_neg (A : ℝ × ℝ → ℝ × ℝ) :
    Cartesian.planarCurl (-A) = -Cartesian.planarCurl A := by
  funext p
  simp only [Cartesian.planarCurl, Pi.neg_apply, Prod.fst_neg, Prod.snd_neg, deriv.fun_neg]
  ring

/-- Smoothness of a prescribed gradient raises any differentiable primitive
 to C². No regularity of a purported gauge is imposed beyond differentiability. -/
theorem planar_contDiff_of_gradient (f : ℝ × ℝ → ℝ)
    (hf : Differentiable ℝ f) (hg : ContDiff ℝ 1 (planarGradient f)) :
    ContDiff ℝ 2 f := by
  apply (contDiff_succ_iff_fderiv_apply (n := 1)).2
  refine ⟨hf, by simp, fun d => ?_⟩
  have he : (fun p => fderiv ℝ f p d) =
      fun p => d.1 * (planarGradient f p).1 + d.2 * (planarGradient f p).2 := by
    funext p
    have hd : d = d.1 • ((1, 0) : ℝ × ℝ) + d.2 • (0, 1) := by
      ext <;> simp
    calc
      fderiv ℝ f p d = fderiv ℝ f p (d.1 • (1, 0) + d.2 • (0, 1)) := congrArg _ hd
      _ = _ := by rw [map_add, map_smul, map_smul]; rfl
  rw [he]
  exact (contDiff_const.mul hg.fst).add (contDiff_const.mul hg.snd)

/-- Gauge equivalence with an everywhere differentiable scalar and actual
Fréchet gradient. C² is a consequence when the prescribed field is smooth. -/
def PlanarGaugeEquivalent (A B : ℝ × ℝ → ℝ × ℝ) : Prop :=
  ∃ f : ℝ × ℝ → ℝ, Differentiable ℝ f ∧ ∀ p, B p = A p + planarGradient f p

theorem opposite_not_planar_gauge (A : ℝ × ℝ → ℝ × ℝ)
    (hA : ContDiff ℝ ∞ A) (hc : Cartesian.planarCurl A ≠ 0) :
    ¬PlanarGaugeEquivalent A (-A) := by
  rintro ⟨f, hf, hg⟩
  have hgrad : planarGradient f = (-2 : ℝ) • A := by
    funext p
    have hx := congrArg Prod.fst (hg p)
    have hy := congrArg Prod.snd (hg p)
    simp only [Pi.neg_apply, Prod.fst_neg, Prod.fst_add] at hx
    simp only [Pi.neg_apply, Prod.snd_neg, Prod.snd_add] at hy
    apply Prod.ext
    · change (planarGradient f p).1 = (-2 : ℝ) * (A p).1
      linarith
    · change (planarGradient f p).2 = (-2 : ℝ) * (A p).2
      linarith
  have hf2 : ContDiff ℝ 2 f := planar_contDiff_of_gradient f hf (by
    rw [hgrad]
    exact (hA.of_le (by simp)).const_smul (-2 : ℝ))
  have hzero := curl_gradient f hf2
  rw [hgrad] at hzero
  have hscale : Cartesian.planarCurl ((-2 : ℝ) • A) = (-2 : ℝ) • Cartesian.planarCurl A := by
    funext p
    simp only [Cartesian.planarCurl, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, deriv_const_mul_field]
    ring
  rw [hscale] at hzero
  apply hc
  funext p
  have h := congrFun hzero p
  change (-2 : ℝ) * Cartesian.planarCurl A p = 0 at h
  change Cartesian.planarCurl A p = 0
  linarith

/-- A three-dimensional scalar gauge must also induce a planar gauge on z=0. -/
def SpatialGaugeEquivalent (A B : ℝ × ℝ → ℝ × ℝ) : Prop :=
  ∃ f : ConstructionData.Space → ℝ, Differentiable ℝ f ∧
    (∀ p z, (B p).1 = (A p).1 + fderiv ℝ f (p, z) ((1, 0), 0)) ∧
    (∀ p z, (B p).2 = (A p).2 + fderiv ℝ f (p, z) ((0, 1), 0))

theorem spatial_implies_planar (A B : ℝ × ℝ → ℝ × ℝ) :
    SpatialGaugeEquivalent A B → PlanarGaugeEquivalent A B := by
  rintro ⟨f, hf, hx, hy⟩
  let g : ℝ × ℝ → ℝ := fun p => f (p, 0)
  have hg : Differentiable ℝ g := hf.comp (differentiable_id.prodMk (differentiable_const (0 : ℝ)))
  refine ⟨g, hg, fun p => ?_⟩
  have hi : HasFDerivAt (fun q : ℝ × ℝ => (q, (0 : ℝ)))
      ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod 0) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const (0 : ℝ) p)
  have hd := (hf (p, 0)).hasFDerivAt.comp p hi
  change HasFDerivAt g _ p at hd
  apply Prod.ext
  · simpa only [planarGradient, hd.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      zero_apply, Prod.fst_add] using hx p 0
  · simpa only [planarGradient, hd.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      zero_apply, Prod.snd_add] using hy p 0

theorem bounded_opposite_not_gauge (t : ℝ) (ht : 0 < t) :
    ¬SpatialGaugeEquivalent (Cartesian.boundedVector t) (-Cartesian.boundedVector t) := by
  intro h
  exact opposite_not_planar_gauge _ (Cartesian.boundedVector_contDiff t ht.le)
    (Cartesian.bounded_curl_nonzero t ht) (spatial_implies_planar _ _ h)

theorem gaussian_opposite_not_gauge (t : ℝ) (ht : 0 < t) :
    ¬SpatialGaugeEquivalent (Cartesian.gaussianVector t) (-Cartesian.gaussianVector t) := by
  intro h
  exact opposite_not_planar_gauge _ (Cartesian.gaussianVector_contDiff t ht.le)
    (Cartesian.gaussian_curl_nonzero t ht) (spatial_implies_planar _ _ h)

/-- Every field refers to the actual functions, operators and differential
current. Both ground states are isolated and their eigenspaces are simple. -/
structure PairedGroundStates (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ)
    (W : ℝ → ℝ) (E : ℝ) (ψ : Space × Space → ℂ) : Prop where
  realized : ∃ F : FermionRealization.System,
    FermionRealization.Facts F A V W ∧ GroundState F E ψ ∧
    FermionRealization.Facts (reverseOperator F) (-A) V W ∧
    GroundState (reverseOperator F) E (fun p => conj (ψ p))
  normalized : (∫ p, Complex.normSq (ψ p)) = 1
  reversed_normalized : (∫ p, Complex.normSq (conj (ψ p))) = 1
  positive_density : ∀ x, 0 < density ψ x
  equal_density : ∀ x, density (fun p => conj (ψ p)) x = density ψ x
  zero_currents : ∀ᵐ x : Space, ∀ d : Space,
    current A ψ x d = 0 ∧ current (-A) (fun p => conj (ψ p)) x d = 0
  gauge_inequivalent : ¬SpatialGaugeEquivalent A (-A)

theorem paired_ground_states (library : StandardAntiunitaryLibrary)
    (F : FermionRealization.System) (A : ℝ × ℝ → ℝ × ℝ)
    (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ) (E : ℝ) (ψ : Space × Space → ℂ)
    (hF : FermionRealization.Facts F A V W) (hg : GroundState F E ψ)
    (hn : (∫ p, Complex.normSq (ψ p)) = 1)
    (hρ : ∀ x, 0 < density ψ x)
    (hj : ∀ᵐ x : Space, ∀ d : Space, current A ψ x d = 0)
    (hneq : ¬SpatialGaugeEquivalent A (-A)) : PairedGroundStates A V W E ψ := by
  refine ⟨⟨F, hF, hg, reverse_facts library F A V W hF,
    reverse_ground library F hF.selfadjoint E ψ hg⟩,
    hn, ?_, hρ, density_conjugate ψ, ?_, hneq⟩
  · rw [normalization_conjugate, hn]
  · filter_upwards [hj] with x hx
    intro d
    exact ⟨hx d, by rw [current_conjugate, hx d, neg_zero]⟩

/-- The bounded counterexample with actual opposite vector potentials and
actual conjugate wavefunctions. All chosen-profile spectral inputs are already
proved before applying the universal antiunitary operator theorem. -/
theorem bounded_counterexample
    (planar : PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : AxialRealization.StandardAxialLibrary)
    (tensor : StandardTensorLibrary) (fermion : StandardFermionLibrary)
    (reversal : StandardAntiunitaryLibrary) :
    ∃ t : ℝ, 0 < t ∧
      ContDiff ℝ ∞ (ConstructionData.bounded3Vector t) ∧
      ContDiff ℝ ∞ (-ConstructionData.bounded3Vector t) ∧
      ContDiff ℝ ∞ (ConstructionData.bounded3Scalar t 5) ∧
      (∃ C : ℝ, ∀ p, ‖ConstructionData.bounded3Vector t p‖ ≤ C ∧
        ‖(-ConstructionData.bounded3Vector t) p‖ ≤ C) ∧
      (∃ C : ℝ, ∀ p, |ConstructionData.bounded3Scalar t 5 p| ≤ C) ∧
      PairedGroundStates (Cartesian.boundedVector t) (Cartesian.boundedScalar t) (Axial.potential 5)
        20 (fun p => ConcreteSlater.wave t 5 p.1 p.2) := by
  obtain ⟨t, ht, hAs, hVs, hAb, hVb, _, T, F, _, _, _, _, hF, hg, hn, hρ, hj⟩ :=
    FermionRealization.bounded_example planar axial tensor fermion
  refine ⟨t, ht, hAs, hAs.neg, hVs, ?_, hVb, ?_⟩
  · obtain ⟨C, hC⟩ := hAb
    exact ⟨C, fun p => ⟨hC p, by simpa only [Pi.neg_apply, norm_neg] using hC p⟩⟩
  · apply paired_ground_states reversal F _ _ _ _ _ hF hg hn
    · exact hρ
    · filter_upwards [hj] with x hx
      intro d
      rw [bounded_current_eq]
      exact hx d
    · exact bounded_opposite_not_gauge t ht

theorem gaussian_current_eq (t c : ℝ) (x d : Space) :
    current (Cartesian.gaussianVector t) (fun p => GaussianSlater.wave t c p.1 p.2) x d =
      GaussianSlater.physicalCurrent t c x d := by
  simp only [current, density, fieldPairing, GaussianSlater.physicalCurrent,
    GaussianSlater.fieldPairing, GaussianSlater.realCoordinates,
    ConstructionData.gaussian3Vector, Complex.star_def, zero_mul, add_zero]

/-- The Gaussian counterexample, with the exact shared positive density. -/
theorem gaussian_counterexample
    (planar : PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : GaussianAxial.StandardOscillatorLibrary)
    (tensor : StandardTensorLibrary) (fermion : StandardFermionLibrary)
    (reversal : StandardAntiunitaryLibrary) (c : ℝ) (hc : 1 < c) :
    ∃ t : ℝ, 0 < t ∧
      ContDiff ℝ ∞ (ConstructionData.gaussian3Vector t) ∧
      ContDiff ℝ ∞ (-ConstructionData.gaussian3Vector t) ∧
      ContDiff ℝ ∞ (ConstructionData.gaussian3Scalar t c) ∧
      (∃ C : ℝ, ∀ p, ‖ConstructionData.gaussian3Vector t p‖ ≤ C ∧
        ‖(-ConstructionData.gaussian3Vector t) p‖ ≤ C) ∧
      PairedGroundStates (Cartesian.gaussianVector t) (Cartesian.gaussianScalar t) (GaussianAxial.potential c)
        2 (fun p => GaussianSlater.wave t c p.1 p.2) ∧
      (∀ x, density (fun p => GaussianSlater.wave t c p.1 p.2) x =
        (2 / Real.pi) * Real.sqrt (c / Real.pi) * Real.exp (-‖x.1‖ ^ 2 - c * x.2 ^ 2)) := by
  obtain ⟨t, ht, hAs, hVs, hAb, _, F, hF, hg, hn, hρ, hj⟩ :=
    GaussianFermion.gaussian_example planar axial tensor fermion c hc
  refine ⟨t, ht, hAs, hAs.neg, hVs, ?_, ?_, hρ⟩
  · obtain ⟨C, hC⟩ := hAb
    exact ⟨C, fun p => ⟨hC p, by simpa only [Pi.neg_apply, norm_neg] using hC p⟩⟩
  · apply paired_ground_states reversal F _ _ _ _ _ hF hg hn
    · intro x
      change 0 < 2 * ∫ y, Complex.normSq (GaussianSlater.wave t c x y)
      rw [hρ x]
      have hc0 : 0 < c := by linarith
      positivity
    · filter_upwards [hj] with x hx
      intro d
      rw [gaussian_current_eq]
      exact hx d
    · exact gaussian_opposite_not_gauge t ht

end MagHK.CounterexamplePair
