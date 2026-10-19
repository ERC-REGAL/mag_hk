import MagHK.MonopoleCovariance

/-! The closed magnetic form is invariant by the actual gauge and rotation action. -/
noncomputable section
namespace MagHK.MonopoleCovariance
open MeasureTheory Set Filter
open MagHK.MonopoleRealization MagHK.MonopoleCurrent MagHK.SpinChart
open scoped ComplexConjugate
set_option maxHeartbeats 1000000

private theorem complex_integral_re {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ := (integral_re (𝕜 := ℂ) hf).symm

private theorem complex_sum_re {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    (∑ i, f i).re = ∑ i, (f i).re := map_sum Complex.reAddGroupHom f Finset.univ

def vectorEnergy (v : CVector) : ℝ := ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2

theorem vectorEnergy_rotate (R : MagHK.MonopoleQuadrature.Space ≃ₗᵢ[ℝ] MagHK.MonopoleQuadrature.Space) (v : CVector) :
    vectorEnergy (rotateVector R v) = vectorEnergy v := by simp [vectorEnergy, rotateVector]

theorem vectorEnergy_complexScale (z : ℂ) (v : CVector) :
    vectorEnergy (complexScale z v) = Complex.normSq z * vectorEnergy v := by
  simp only [vectorEnergy, complexScale, norm_sub_sq_real, norm_add_sq_real,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm v.2 v.1, Complex.normSq_apply]
  ring

def kineticDensity (S : MagneticFormSystem) (ψ : S.domain) (p : Chart × Chart) : ℝ :=
  ∑ i : Fin 2, ∑ k : Fin 3, Complex.normSq (S.pi i k ψ p)

def energyDensity (S : MagneticFormSystem) (W : Chart × Chart → ℝ)
    (ψ : S.domain) (p : Chart × Chart) : ℝ :=
  kineticDensity S ψ p + fullPotential W p * Complex.normSq ((ψ : PairState) p)

theorem chart_angle_ae : ∀ᵐ x ∂chartMeasure, x.2.1 ∈ Icc (-1 : ℝ) 1 :=
  Measure.quasiMeasurePreserving_snd.ae MagHK.MonopoleTrial.angle_ae

theorem pair_angle_ae : ∀ᵐ p ∂pairMeasure,
    p.1.2.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2.2.1 ∈ Icc (-1 : ℝ) 1 := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae chart_angle_ae,
    Measure.quasiMeasurePreserving_snd.ae chart_angle_ae] with p hp hq
  exact ⟨hp, hq⟩

theorem movedPair_measurePreserving (q : ℤ) (R : AngularMomentumAction q) (U : MagHK.Spin.Group) :
    MeasurePreserving (movedPair U) pairMeasure pairMeasure :=
  (R.chart_measure U).prod (R.chart_measure U)

theorem covariantVector_energy (S : MagneticFormSystem) (ψ : S.domain) (i : Fin 2)
    (p : Chart × Chart) (hp : p.1.2.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2.2.1 ∈ Icc (-1 : ℝ) 1) :
    vectorEnergy (covariantVector S ψ i p) = ∑ k : Fin 3, Complex.normSq (S.pi i k ψ p) := by
  have hx : (if i = 0 then p.1 else p.2).2.1 ∈ Icc (-1 : ℝ) 1 := by
    split_ifs <;> tauto
  exact frame_sum_normSq (if i = 0 then p.1 else p.2) hx (fun k => S.pi i k ψ p)

theorem kineticDensity_integrable (S : MagneticFormSystem) (ψ : S.domain) :
    Integrable (kineticDensity S ψ) pairMeasure := by
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro k _
  simpa only [real_inner_self_eq_norm_sq, Complex.normSq_eq_norm_sq] using
    (L2.integrable_inner (𝕜 := ℝ) (S.pi i k ψ) (S.pi i k ψ))

theorem potentialDensity_integrable (q : ℤ) (S : MagneticFormSystem) (F : FermionSystem)
    (W : Chart × Chart → ℝ) (hS : MagneticFormFacts S F q W) (ψ : S.domain) :
    Integrable (fun p => fullPotential W p * Complex.normSq ((ψ : PairState) p)) pairMeasure := by
  have h := (hS.potential_integrable ψ ψ).re
  apply h.congr
  exact Eventually.of_forall fun p => by
    change ((fullPotential W p : ℂ) * conj ((ψ : PairState) p) * (ψ : PairState) p).re = _
    rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self]
    simp

theorem energyDensity_integrable (q : ℤ) (S : MagneticFormSystem) (F : FermionSystem)
    (W : Chart × Chart → ℝ) (hS : MagneticFormFacts S F q W) (ψ : S.domain) :
    Integrable (energyDensity S W ψ) pairMeasure :=
  (kineticDensity_integrable S ψ).add (potentialDensity_integrable q S F W hS ψ)

theorem formPairing_re (q : ℤ) (S : MagneticFormSystem) (F : FermionSystem)
    (W : Chart × Chart → ℝ) (hS : MagneticFormFacts S F q W) (ψ : S.domain) :
    (formPairing S W ψ ψ).re = ∫ p, energyDensity S W ψ p ∂pairMeasure := by
  rw [show (fun p => energyDensity S W ψ p) = (fun p => kineticDensity S ψ p +
    fullPotential W p * Complex.normSq ((ψ : PairState) p)) from rfl,
    integral_add (kineticDensity_integrable S ψ) (potentialDensity_integrable q S F W hS ψ)]
  unfold formPairing kineticDensity
  rw [Complex.add_re]
  congr 1
  · simp only [complex_sum_re]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro k _
        rw [L2.inner_def, complex_integral_re (L2.integrable_inner (𝕜 := ℂ) (S.pi i k ψ) (S.pi i k ψ))]
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by simp only [RCLike.inner_apply',
          ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      · intro k _
        simpa only [real_inner_self_eq_norm_sq, Complex.normSq_eq_norm_sq] using
          (L2.integrable_inner (𝕜 := ℝ) (S.pi i k ψ) (S.pi i k ψ))
    · intro i _
      apply integrable_finset_sum
      intro k _
      simpa only [real_inner_self_eq_norm_sq, Complex.normSq_eq_norm_sq] using
        (L2.integrable_inner (𝕜 := ℝ) (S.pi i k ψ) (S.pi i k ψ))
  · rw [complex_integral_re (hS.potential_integrable ψ ψ)]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      dsimp only
      rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self]
      simp

theorem energyDensity_rotation (q : ℤ) (R : AngularMomentumAction q)
    (S : MagneticFormSystem) (F : FermionSystem) (W : Chart × Chart → ℝ)
    (hS : MagneticFormFacts S F q W) (A : MagneticRotations q R S F W hS)
    (hW : RotationInvariantPotential q R W) (U : MagHK.Spin.Group) (ψ : S.domain) :
    (fun p => energyDensity S W (A.lift U ψ) p) =ᵐ[pairMeasure]
      fun p => energyDensity S W ψ (movedPair U p) := by
  have hw : ∀ᵐ p ∂pairMeasure, (A.lift U ψ : PairState) p =
      pairPhase q U p * (ψ : PairState) (movedPair U p) := by
    rw [A.lift_state]
    exact R.pair_formula U (asFermion S F q W hS ψ)
  have hpm := (movedPair_measurePreserving q R U).quasiMeasurePreserving.ae pair_angle_ae
  filter_upwards [pair_angle_ae, hpm, hw, A.covariant_vector U ψ 0,
    A.covariant_vector U ψ 1, hW U] with p hp hmp hw h0 h1 hpot
  unfold energyDensity
  congr 1
  · unfold kineticDensity
    apply Finset.sum_congr rfl
    intro i _
    rw [← covariantVector_energy S (A.lift U ψ) i p hp,
      ← covariantVector_energy S ψ i (movedPair U p) hmp]
    have hv : covariantVector S (A.lift U ψ) i p = complexScale (pairPhase q U p)
        (rotateVector (R.rotation U⁻¹).symm (covariantVector S ψ i (movedPair U p))) := by
      fin_cases i <;> assumption
    rw [hv, vectorEnergy_complexScale, pairPhase_normSq, one_mul, vectorEnergy_rotate]
  · rw [hw, Complex.normSq_mul, pairPhase_normSq, one_mul]
    congr 1
    change p.1.1 ^ 2 + p.2.1 ^ 2 + W p =
      p.1.1 ^ 2 + p.2.1 ^ 2 + W (movedPair U p)
    rw [hpot]

theorem form_energy_rotation (q : ℤ) (R : AngularMomentumAction q)
    (S : MagneticFormSystem) (F : FermionSystem) (W : Chart × Chart → ℝ)
    (hS : MagneticFormFacts S F q W) (A : MagneticRotations q R S F W hS)
    (hW : RotationInvariantPotential q R W) (U : MagHK.Spin.Group) (ψ : S.domain) :
    (formPairing S W (A.lift U ψ) (A.lift U ψ)).re = (formPairing S W ψ ψ).re := by
  rw [formPairing_re q S F W hS, formPairing_re q S F W hS,
    integral_congr_ae (energyDensity_rotation q R S F W hS A hW U ψ)]
  have hm : AEStronglyMeasurable (energyDensity S W ψ)
      (Measure.map (movedPair U) pairMeasure) := by
    rw [(movedPair_measurePreserving q R U).map_eq]
    exact (energyDensity_integrable q S F W hS ψ).aestronglyMeasurable
  have h := integral_map (movedPair_measurePreserving q R U).measurable.aemeasurable hm
  rw [(movedPair_measurePreserving q R U).map_eq] at h
  exact h.symm

end MagHK.MonopoleCovariance
