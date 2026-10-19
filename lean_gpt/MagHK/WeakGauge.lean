import MagHK.CounterexamplePair
import MagHK.MonopoleFlux
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Gauge obstruction for genuine weak gradients, including almost-everywhere
Sobolev gauge identities. A universal local gradient regularity theorem turns
a C1 prescribed weak derivative into a C2 representative. The previously
proved classical curl obstructions then apply to the same actual fields.
-/
noncomputable section
namespace MagHK.WeakGauge
open MeasureTheory Set
open scoped ContDiff

section Weak
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasureSpace X] [BorelSpace X]

/-- Literal distributional gradient on an open set. -/
structure WeakGradient (s : Set X) (f : X → ℝ) (G : X → X →L[ℝ] ℝ) : Prop where
  locally_integrable : LocallyIntegrableOn f s (volume : Measure X)
  test : ∀ η : X → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ s →
    ∀ d : X, (∫ x, f x * fderiv ℝ η x d) = -(∫ x, G x d * η x)

end Weak

/-- The standard local regularity theorem for the distributional gradient.
It applies to every scalar function and prescribed C1 covector field. There
is no magnetic field, curvature or gauge-equivalence conclusion in it. -/
def GradientRegularity (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasureSpace X] [BorelSpace X] : Prop :=
  ∀ (s : Set X), IsOpen s → ∀ (f : X → ℝ) (G : X → X →L[ℝ] ℝ),
    ContDiffOn ℝ 1 G s → WeakGradient s f G →
    ∃ g : X → ℝ, ContDiffOn ℝ 2 g s ∧
      (∀ᵐ x, x ∈ s → f x = g x) ∧ ∀ x ∈ s, HasFDerivAt g (G x) x

def StandardGradientRegularityLibrary : Prop :=
  GradientRegularity (ℝ × ℝ) ∧ GradientRegularity MagHK.ConstructionData.Space

abbrev Spatial := MagHK.ConstructionData.Space

def xProjection : Spatial →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)

def yProjection : Spatial →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)

def spatialCovector (A : ℝ × ℝ → ℝ × ℝ) (x : Spatial) : Spatial →L[ℝ] ℝ :=
  (A x.1).1 • xProjection + (A x.1).2 • yProjection

theorem spatialCovector_contDiff (A : ℝ × ℝ → ℝ × ℝ) (hA : ContDiff ℝ 1 A) :
    ContDiff ℝ 1 (spatialCovector A) := by
  exact (((hA.comp contDiff_fst).fst).smul contDiff_const).add
    (((hA.comp contDiff_fst).snd).smul contDiff_const)

def SpatialGaugeEquivalent (A B : ℝ × ℝ → ℝ × ℝ) : Prop :=
  ∃ f : Spatial → ℝ, WeakGradient univ f (spatialCovector (B - A))

theorem spatial_implies_classical (regularity : GradientRegularity Spatial)
    (A B : ℝ × ℝ → ℝ × ℝ) (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B)
    (h : SpatialGaugeEquivalent A B) : MagHK.CounterexamplePair.SpatialGaugeEquivalent A B := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, _hg, _, hd⟩ := regularity univ isOpen_univ f (spatialCovector (B - A))
    (spatialCovector_contDiff (B - A) (hB.sub hA)).contDiffOn hf
  refine ⟨g, fun x => (hd x (mem_univ x)).differentiableAt, ?_, ?_⟩
  · intro p z
    rw [(hd (p, z) (mem_univ _)).fderiv]
    simp [spatialCovector, xProjection, yProjection]
  · intro p z
    rw [(hd (p, z) (mem_univ _)).fderiv]
    simp [spatialCovector, xProjection, yProjection]

theorem bounded_opposite_not_weak_gauge (regularity : StandardGradientRegularityLibrary)
    (t : ℝ) (ht : 0 < t) :
    ¬SpatialGaugeEquivalent (MagHK.Cartesian.boundedVector t) (-MagHK.Cartesian.boundedVector t) := by
  intro h
  exact MagHK.CounterexamplePair.bounded_opposite_not_gauge t ht
    (spatial_implies_classical regularity.2 _ _
      ((MagHK.Cartesian.boundedVector_contDiff t ht.le).of_le (by norm_num))
      (((MagHK.Cartesian.boundedVector_contDiff t ht.le).neg).of_le (by norm_num)) h)

theorem gaussian_opposite_not_weak_gauge (regularity : StandardGradientRegularityLibrary)
    (t : ℝ) (ht : 0 < t) :
    ¬SpatialGaugeEquivalent (MagHK.Cartesian.gaussianVector t) (-MagHK.Cartesian.gaussianVector t) := by
  intro h
  exact MagHK.CounterexamplePair.gaussian_opposite_not_gauge t ht
    (spatial_implies_classical regularity.2 _ _
      ((MagHK.Cartesian.gaussianVector_contDiff t ht.le).of_le (by norm_num))
      (((MagHK.Cartesian.gaussianVector_contDiff t ht.le).neg).of_le (by norm_num)) h)

def monopoleCovector (q q' : ℤ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (MagHK.MonopoleRealization.northCoefficient q' p.1 -
    MagHK.MonopoleRealization.northCoefficient q p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem monopoleCovector_contDiff (q q' : ℤ) : ContDiff ℝ 1 (monopoleCovector q q') := by
  unfold monopoleCovector MagHK.MonopoleRealization.northCoefficient
  fun_prop

def LocallyGaugeEquivalent (q q' : ℤ) : Prop :=
  ∃ s : Set (ℝ × ℝ), IsOpen s ∧ (0, 0) ∈ s ∧ ∃ f : (ℝ × ℝ) → ℝ,
    WeakGradient s f (monopoleCovector q q')

theorem monopole_implies_classical (regularity : GradientRegularity (ℝ × ℝ))
    (q q' : ℤ) (h : LocallyGaugeEquivalent q q') :
    MagHK.MonopoleFlux.LocallyGaugeEquivalent q q' := by
  obtain ⟨s, hs, hp, f, hf⟩ := h
  obtain ⟨g, hg, _, hd⟩ := regularity s hs f (monopoleCovector q q')
    (monopoleCovector_contDiff q q').contDiffOn hf
  refine ⟨s, hs, hp, g, hg, ?_⟩
  intro p hp
  rw [(hd p hp).fderiv]
  simp [monopoleCovector]

theorem weak_gauge_charge_eq (regularity : StandardGradientRegularityLibrary)
    (q q' : ℤ) (h : LocallyGaugeEquivalent q q') : q = q' :=
  MagHK.MonopoleFlux.local_gauge_charge_eq q q' (monopole_implies_classical regularity.1 q q' h)

theorem opposite_monopoles_not_weak_gauge (regularity : StandardGradientRegularityLibrary) :
    ¬LocallyGaugeEquivalent 1 (-1) := by
  intro h
  have he := weak_gauge_charge_eq regularity 1 (-1) h
  norm_num at he

end MagHK.WeakGauge
