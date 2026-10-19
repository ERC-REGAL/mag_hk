import MagHK.PassiveSpin

/-! The four-particle counterexamples in the submission's `rem:spin`.
The spectral isolation already supplied by exterior filling gives an actual
positive excitation gap. The same potentials also retain their proved weak
gauge obstruction. No additional background library is required. -/
noncomputable section
namespace MagHK.PassiveSpin

/-- An isolated spectral ground state has a positive excitation gap. -/
theorem GroundState.excitation_gap {N : ℕ} {H : System N} {E : ℝ}
    {f : Configuration N → ℂ} (h : GroundState N H E f) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ e ∈ MagHK.OperatorModel.spectrum H,
      E < e → E + δ ≤ e := by
  obtain ⟨δ, hδ, hisolated⟩ := h.2.2.2
  refine ⟨δ, hδ, fun e he hEe => ?_⟩
  by_contra hlt
  have hnear : |e - E| < δ := by
    rw [abs_of_pos (sub_pos.mpr hEe)]
    linarith
  exact (ne_of_gt hEe) (hisolated e he hnear)

/-- One positive gap can be chosen for both opposite-field Hamiltonians. -/
theorem PairedResult.excitation_gap
    {A : ℝ × ℝ → ℝ × ℝ} {V : ℝ × ℝ → ℝ} {W : ℝ → ℝ}
    {e₀ e₁ : ℝ} {f g : Space → ℂ} (R : PairedResult A V W e₀ e₁ f g) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ E,
      (E ∈ MagHK.OperatorModel.spectrum R.filled.operator ∨
        E ∈ MagHK.OperatorModel.spectrum (reverseOperator 4 R.filled.operator)) →
      2 * (e₀ + e₁) < E → 2 * (e₀ + e₁) + δ ≤ E := by
  obtain ⟨deltaPlus, hdeltaPlus, hplus⟩ := R.filled.ground.excitation_gap
  obtain ⟨deltaMinus, hdeltaMinus, hminus⟩ := R.reversed_ground.excitation_gap
  refine ⟨min deltaPlus deltaMinus, lt_min hdeltaPlus hdeltaMinus, fun E hE hground => ?_⟩
  rcases hE with hE | hE
  · calc
      2 * (e₀ + e₁) + min deltaPlus deltaMinus ≤ 2 * (e₀ + e₁) + deltaPlus := by
        linarith [min_le_left deltaPlus deltaMinus]
      _ ≤ E := hplus E hE hground
  · calc
      2 * (e₀ + e₁) + min deltaPlus deltaMinus ≤ 2 * (e₀ + e₁) + deltaMinus := by
        linarith [min_le_right deltaPlus deltaMinus]
      _ ≤ E := hminus E hE hground

/-- The spin-summed coincidence is paired with gauge inequivalence of the
same actual vector potentials. The scalar potential is identical for both
operators in `paired`. -/
structure CounterexampleResult (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ)
    (e₀ e₁ : ℝ) (f g : Space → ℂ) where
  paired : PairedResult A V W e₀ e₁ f g
  not_weak_gauge : ¬ MagHK.WeakGauge.SpatialGaugeEquivalent A (-A)

/-- The bounded construction gives an unrestricted four-particle
counterexample and the two-particle exclusion for the same parameter. -/
theorem bounded_passive_spin_counterexample
    (planar : MagHK.PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : MagHK.AxialRealization.StandardAxialLibrary)
    (tensor : MagHK.TensorRealization.StandardTensorLibrary)
    (spin : StandardSpinLibrary) (exterior : StandardExteriorLibrary)
    (reduction : StandardSlaterReductionLibrary) (reversal : StandardSpinReversalLibrary)
    (regularity : MagHK.WeakGauge.StandardGradientRegularityLibrary) :
    ∃ t : ℝ, 0 < t ∧
      Nonempty (CounterexampleResult (MagHK.Cartesian.boundedVector t)
        (MagHK.Cartesian.boundedScalar t) (MagHK.Axial.potential 5) 0 20
        (MagHK.CartesianOrbitals.orbitalZero t 5) (MagHK.CartesianOrbitals.orbitalMinus t 5)) ∧
      Nonempty (UnrestrictedTwoResult (MagHK.Cartesian.boundedVector t)
        (MagHK.Cartesian.boundedScalar t) (MagHK.Axial.potential 5) 0 20
        (MagHK.CartesianOrbitals.orbitalZero t 5) (MagHK.CartesianOrbitals.orbitalMinus t 5)) := by
  obtain ⟨t, ht, ⟨R⟩, htwo⟩ :=
    bounded_passive_spin_complete planar axial tensor spin exterior reduction reversal
  exact ⟨t, ht, ⟨⟨R, MagHK.WeakGauge.bounded_opposite_not_weak_gauge regularity t ht⟩⟩,
    htwo⟩

/-- Every c > 1 in the Gaussian construction gives the analogous
unrestricted four-particle counterexample and two-particle exclusion. -/
theorem gaussian_passive_spin_counterexample
    (planar : MagHK.PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : MagHK.GaussianAxial.StandardOscillatorLibrary)
    (tensor : MagHK.TensorRealization.StandardTensorLibrary)
    (spin : StandardSpinLibrary) (exterior : StandardExteriorLibrary)
    (reduction : StandardSlaterReductionLibrary) (reversal : StandardSpinReversalLibrary)
    (regularity : MagHK.WeakGauge.StandardGradientRegularityLibrary)
    (c : ℝ) (hc : 1 < c) :
    ∃ t : ℝ, 0 < t ∧
      Nonempty (CounterexampleResult (MagHK.Cartesian.gaussianVector t)
        (MagHK.Cartesian.gaussianScalar t) (MagHK.GaussianAxial.potential c) 0 2
        (MagHK.GaussianOrbitals.orbitalZero t c) (MagHK.GaussianOrbitals.orbitalMinus t c)) ∧
      Nonempty (UnrestrictedTwoResult (MagHK.Cartesian.gaussianVector t)
        (MagHK.Cartesian.gaussianScalar t) (MagHK.GaussianAxial.potential c) 0 2
        (MagHK.GaussianOrbitals.orbitalZero t c) (MagHK.GaussianOrbitals.orbitalMinus t c)) := by
  obtain ⟨t, ht, ⟨R⟩, htwo⟩ :=
    gaussian_passive_spin_complete planar axial tensor spin exterior reduction reversal c hc
  exact ⟨t, ht, ⟨⟨R, MagHK.WeakGauge.gaussian_opposite_not_weak_gauge regularity t ht⟩⟩,
    htwo⟩

end MagHK.PassiveSpin
