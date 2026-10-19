import MagHK.OperatorCompactness
import MagHK.CounterexamplePair

/-! Actual compact resolvents for the Gaussian Hamiltonians. The only new
external input is the general Rellich compactness theorem for smooth magnetic
Schrödinger operators with bounded vector potential and a quadratically
confining scalar potential, on one-particle space and its exterior square.
The selected scalar lower bound and conjugation of the compact inverse are
proved below. -/
noncomputable section
namespace MagHK.GaussianCompactness
open MeasureTheory Set
open MagHK.TensorRealization MagHK.FermionRealization MagHK.OperatorTimeReversal
open MagHK.CounterexamplePair MagHK.OperatorModel
open scoped ContDiff ComplexConjugate

/-- Literal coercivity of the three-dimensional scalar potential. -/
def QuadraticConfinement (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ) : Prop :=
  ∃ κ C : ℝ, 0 < κ ∧ ∀ p z, κ * (p.1 ^ 2 + p.2 ^ 2 + z ^ 2) - C ≤ V p + W z

/-- General compact form-embedding and essential-selfadjointness results.
Both conclusions concern the supplied actual selfadjoint differential
realization, so they cannot select an unrelated operator with convenient
spectrum. No eigenstate or manuscript coefficient appears in this premise. -/
structure StandardConfiningLibrary : Prop where
  one_body : ∀ (T : TensorRealization.System) A V W,
    ContDiff ℝ ∞ A → ContDiff ℝ ∞ V → ContDiff ℝ ∞ W →
    (∃ C : ℝ, ∀ p, ‖A p‖ ≤ C) → QuadraticConfinement V W →
    OneBodyRealization T A V W → CompactResolvent T
  exterior_square : ∀ (F : FermionRealization.System) A V W,
    ContDiff ℝ ∞ A → ContDiff ℝ ∞ V → ContDiff ℝ ∞ W →
    (∃ C : ℝ, ∀ p, ‖A p‖ ≤ C) → QuadraticConfinement V W →
    FermionRealization.Facts F A V W → CompactResolvent F

theorem reverse_compact (F : FermionRealization.System) (h : CompactResolvent F) :
    CompactResolvent (reverseOperator F) := by
  obtain ⟨E, R, hR, hd, hr, hl⟩ := h
  let K : FermionState →L[ℝ] FermionState := conjugation.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨E, K.comp (R.comp K), (hR.comp_clm K).clm_comp K, ?_, ?_, ?_⟩
  · intro f
    exact reverse_domain F (R (conjugation f)) (hd (conjugation f))
  · intro f hf
    change conjugation (F.map ⟨conjugation (conjugation (R (conjugation f))), _⟩) -
      E • conjugation (R (conjugation f)) = f
    simp only [conjugation_involutive]
    rw [← map_smul, ← map_sub, hr]
    exact conjugation_involutive f
  · intro ψ hψ
    change conjugation (R (conjugation (conjugation (F.map ⟨conjugation ψ, _⟩) - E • ψ))) = ψ
    rw [map_sub, map_smul, conjugation_involutive, hl]
    exact conjugation_involutive ψ

theorem gaussian_quadratic_confinement (t c : ℝ) (ht : 0 ≤ t) (hc : 1 < c) :
    QuadraticConfinement (Cartesian.gaussianScalar t) (GaussianAxial.potential c) := by
  refine ⟨1, 2 + 2 * t + c, by norm_num, fun p z => ?_⟩
  have hq : 0 ≤ Cartesian.radiusSq p := by unfold Cartesian.radiusSq; positivity
  have hv := PartnerAsymptotics.gaussianScalar_quadratic_lower_bound t
    (Real.sqrt (Cartesian.radiusSq p)) ht
  rw [Real.sq_sqrt hq] at hv
  change Cartesian.radiusSq p - (2 + 2 * t) ≤ Cartesian.gaussianScalar t p at hv
  have hc2 : 1 ≤ c ^ 2 := by nlinarith
  have hz := mul_le_mul_of_nonneg_right hc2 (sq_nonneg z)
  change 1 * (p.1 ^ 2 + p.2 ^ 2 + z ^ 2) - (2 + 2 * t + c) ≤
    Cartesian.gaussianScalar t p + (c ^ 2 * z ^ 2 - c)
  unfold Cartesian.radiusSq at hv
  nlinarith

theorem gaussian_one_body_compact (library : StandardConfiningLibrary)
    (t c : ℝ) (ht : 0 ≤ t) (hc : 1 < c) (T : TensorRealization.System)
    (hT : OneBodyRealization T (Cartesian.gaussianVector t) (Cartesian.gaussianScalar t)
      (GaussianAxial.potential c)) : CompactResolvent T :=
  library.one_body T _ _ _ (Cartesian.gaussianVector_contDiff t ht)
    (Cartesian.gaussianScalar_contDiff t ht) (GaussianAxial.potential_smooth c)
    (GaussianPlanar.gaussian_planar_coefficients t ht).vector_bounded
    (gaussian_quadratic_confinement t c ht hc) hT

theorem gaussian_fermion_compact (library : StandardConfiningLibrary)
    (t c : ℝ) (ht : 0 ≤ t) (hc : 1 < c) (F : FermionRealization.System)
    (hF : FermionRealization.Facts F (Cartesian.gaussianVector t) (Cartesian.gaussianScalar t)
      (GaussianAxial.potential c)) : CompactResolvent F ∧ CompactResolvent (reverseOperator F) := by
  have h := library.exterior_square F _ _ _ (Cartesian.gaussianVector_contDiff t ht)
    (Cartesian.gaussianScalar_contDiff t ht) (GaussianAxial.potential_smooth c)
    (GaussianPlanar.gaussian_planar_coefficients t ht).vector_bounded
    (gaussian_quadratic_confinement t c ht hc) hF
  exact ⟨h, reverse_compact F h⟩

/-- The compactness belongs to a realization of the same literal paired
wavefunctions and coefficients as the counterexample. -/
structure CompactPairedGroundStates (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ)
    (W : ℝ → ℝ) (E : ℝ) (ψ : Space × Space → ℂ) : Prop
    extends PairedGroundStates A V W E ψ where
  compact_realized : ∃ F : FermionRealization.System,
    FermionRealization.Facts F A V W ∧ GroundState F E ψ ∧
    FermionRealization.Facts (reverseOperator F) (-A) V W ∧
    GroundState (reverseOperator F) E (fun p => conj (ψ p)) ∧
    CompactResolvent F ∧ CompactResolvent (reverseOperator F)

theorem gaussian_pair_compact (library : StandardConfiningLibrary)
    (t c E : ℝ) (ht : 0 ≤ t) (hc : 1 < c) (ψ : Space × Space → ℂ)
    (h : PairedGroundStates (Cartesian.gaussianVector t) (Cartesian.gaussianScalar t)
      (GaussianAxial.potential c) E ψ) :
    CompactPairedGroundStates (Cartesian.gaussianVector t) (Cartesian.gaussianScalar t)
      (GaussianAxial.potential c) E ψ := by
  refine ⟨h, ?_⟩
  obtain ⟨F, hF, hg, hR, hgr⟩ := h.realized
  exact ⟨F, hF, hg, hR, hgr, gaussian_fermion_compact library t c ht hc F hF⟩

theorem gaussian_compact_counterexample
    (planar : PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : GaussianAxial.StandardOscillatorLibrary)
    (tensor : StandardTensorLibrary) (fermion : StandardFermionLibrary)
    (reversal : StandardAntiunitaryLibrary) (compactness : StandardConfiningLibrary)
    (c : ℝ) (hc : 1 < c) :
    ∃ t : ℝ, 0 < t ∧
      ContDiff ℝ ∞ (ConstructionData.gaussian3Vector t) ∧
      ContDiff ℝ ∞ (-ConstructionData.gaussian3Vector t) ∧
      ContDiff ℝ ∞ (ConstructionData.gaussian3Scalar t c) ∧
      (∃ C : ℝ, ∀ p, ‖ConstructionData.gaussian3Vector t p‖ ≤ C ∧
        ‖(-ConstructionData.gaussian3Vector t) p‖ ≤ C) ∧
      CompactPairedGroundStates (Cartesian.gaussianVector t) (Cartesian.gaussianScalar t)
        (GaussianAxial.potential c) 2 (fun p => GaussianSlater.wave t c p.1 p.2) ∧
      (∀ x, density (fun p => GaussianSlater.wave t c p.1 p.2) x =
        (2 / Real.pi) * Real.sqrt (c / Real.pi) * Real.exp (-‖x.1‖ ^ 2 - c * x.2 ^ 2)) := by
  obtain ⟨t, ht, hA, hR, hV, hb, hpair, hρ⟩ :=
    CounterexamplePair.gaussian_counterexample planar axial tensor fermion reversal c hc
  exact ⟨t, ht, hA, hR, hV, hb, gaussian_pair_compact compactness t c 2 ht.le hc _ hpair, hρ⟩

end MagHK.GaussianCompactness
