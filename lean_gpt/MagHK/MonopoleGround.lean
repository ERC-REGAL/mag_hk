import MagHK.MonopoleRealization
import MagHK.MonopoleExpectation

/-! The actual Coulomb perturbation has a unique isolated monopole ground
state. The two variational inequalities use the computed literal trial
expectation, and the final strict gap is an exact numerical consequence. -/
noncomputable section
namespace MagHK.MonopoleRealization
open MeasureTheory Set
open MagHK.Monopole MagHK.MonopoleTrial MagHK.MonopoleExpectation
open scoped ComplexConjugate

theorem coulomb_measurable : Measurable coulomb := by
  unfold coulomb pairDistance
  fun_prop

theorem coulomb_symmetric (p : Chart × Chart) : coulomb (p.2, p.1) = coulomb p := by
  unfold coulomb pairDistance
  congr 2
  ring

theorem trialWave_coulomb_integrable :
    Integrable (fun p => coulomb p * Complex.normSq (trialWave p)) pairMeasure := by
  have h := regroup_measurePreserving.integrable_comp_of_integrable trialCoulomb_integrable
  apply h.congr
  filter_upwards [] with p
  change Complex.normSq (trial (regroup p)) /
    pairDistance p.1.1 p.2.1 (p.1.2, p.2.2) = coulomb p * Complex.normSq (trialWave p)
  rw [trialWave_eq]
  unfold coulomb
  ring

theorem trialWave_coulomb_bound :
    (∫ p, coulomb p * Complex.normSq (trialWave p) ∂pairMeasure) ≤ coulombBound := by
  rw [trial_coulomb_integral_transport]
  exact trialCoulomb_bound.1

theorem pair_mass (ψ : PairState) :
    (∫ p, Complex.normSq (ψ p) ∂pairMeasure) = ‖ψ‖ ^ 2 := by
  calc
    _ = ∫ p, inner ℝ (ψ p) (ψ p) ∂pairMeasure := by
      apply integral_congr_ae
      exact ae_of_all _ (fun p => by
        dsimp only
        rw [real_inner_self_eq_norm_sq, Complex.normSq_eq_norm_sq])
    _ = inner ℝ ψ ψ := rfl
    _ = ‖ψ‖ ^ 2 := real_inner_self_eq_norm_sq ψ

theorem normalized_eigenvector (F : FermionSystem) (E : ℝ)
    (h : ∃ ψ, OperatorModel.Eigen F E ψ) :
    ∃ ψ : FermionState, OperatorModel.Eigen F E ψ ∧ ‖ψ‖ = 1 := by
  obtain ⟨ψ, hψ, hne, he⟩ := h
  have hn : 0 < ‖ψ‖ := norm_pos_iff.mpr hne
  let c : ℝ := ‖ψ‖⁻¹
  have hc : c ≠ 0 := inv_ne_zero (ne_of_gt hn)
  have hd : c • ψ ∈ F.domain := F.domain.smul_mem c hψ
  refine ⟨c • ψ, ⟨hd, smul_ne_zero hc hne, ?_⟩, ?_⟩
  · change F.map (c • (⟨ψ, hψ⟩ : F.domain)) = E • (c • ψ)
    rw [map_smul, he, smul_comm]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    exact inv_mul_cancel₀ (ne_of_gt hn)

/-- Full concrete gap application on the actual monopole section Hilbert
space. The external premises are universal Friedrichs/spectral, exterior,
Hardy/diamagnetic and closed-form min–max libraries. -/
theorem interacting_ground_state
    (monopole : StandardMonopoleLibrary) (exterior : StandardExteriorLibrary)
    (hardy : StandardCoulombFormLibrary) (minmax : StandardPositivePerturbationLibrary) :
    ∃ F : FermionSystem, ∃ E₀ E₁ : ℝ, ∃ ψ : FermionState,
      FermionFacts F 1 coulomb ∧ OperatorModel.Eigen F E₀ ψ ∧ ‖ψ‖ = 1 ∧
      GroundState F E₀ (fun p => (ψ : PairState) p) ∧
      SpectralGap F E₀ (freeGap - coulombBound) ∧
      freeGap - coulombBound ≤ E₁ - E₀ ∧ (533 / 500 : ℝ) < E₁ - E₀ ∧
      (∫ p, Complex.normSq ((ψ : PairState) p) ∂pairMeasure) = 1 := by
  obtain ⟨H, F₀, _, hF₀, hground, hgap⟩ := free_ground_state monopole exterior
  obtain ⟨F, E₀, E₁, hF, hlevels, hupper, hlower⟩ := minmax 1 coulomb
    coulomb_measurable coulomb_symmetric coulomb_nonnegative (hardy 1)
      F₀ (2 * (2 + Real.sqrt 3)) freeGap trialWave hF₀ hground gap_positive hgap
        trialWave_normalized trialWave_coulomb_integrable
  obtain ⟨hstrict, hdelta, hnumeric⟩ := interacting_gap (2 + Real.sqrt 3) E₀ E₁
    (∫ p, coulomb p * Complex.normSq (trialWave p) ∂pairMeasure)
      hupper hlower trialWave_coulomb_bound
  obtain ⟨ψ, hψ, hn⟩ := normalized_eigenvector F E₀ hlevels.ground_eigen
  refine ⟨F, E₀, E₁, ψ, hF, hψ, hn,
    ⟨⟨ψ, ae_of_all _ (fun _ => rfl), hψ⟩, hlevels.bottom, hlevels.simple_of_lt hstrict⟩,
      ?_, hdelta, hnumeric, ?_⟩
  · intro E hE hne
    have h := hlevels.second_above E hE hne
    linarith
  · rw [pair_mass]
    change ‖ψ‖ ^ 2 = 1
    rw [hn]
    norm_num

end MagHK.MonopoleRealization
