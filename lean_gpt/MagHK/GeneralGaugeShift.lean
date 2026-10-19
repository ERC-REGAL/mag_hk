import MagHK.GeneralGauge

/-! Literal scalar shifts of the many-body operator, form and ground state,
and the paramagnetic current gauge law. No additional operator theorem is
assumed in this module. -/
noncomputable section
namespace MagHK.GeneralGauge
open MeasureTheory Set Filter
open MagHK.ManyBodyTimeReversal
open scoped ComplexConjugate BigOperators ContDiff
set_option maxHeartbeats 1000000

theorem gauge_ground_state (multipliers : StandardPhaseMultiplierLibrary)
    (transport : StandardUnitaryFormLibrary) (N : ℕ) (η : Point → ℝ) (hη : ContDiff ℝ ∞ η)
    (H : System N) (A : Point → Point) (V : Configuration N → ℝ) (b E : ℝ)
    (hH : Facts N H A V b) (ψ : State N) (hψ : GroundState N H E ψ) :
    ∃ U : PhaseUnitary N η, Facts N (gaugeOperator N U.map H) (A + gradient η) V b ∧
      GroundState N (gaugeOperator N U.map H) E (U.map ψ) ∧ ‖U.map ψ‖ = ‖ψ‖ := by
  obtain ⟨U, hU, hs, hm⟩ := gauge_realization multipliers transport N η hη H A V b hH
  refine ⟨U, hU, ⟨gauge_eigen N U.map H E ψ hψ.1, ?_, ?_⟩, U.map.norm_map ψ⟩
  · simpa only [hs] using hψ.2.1
  · simpa only [hm] using hψ.2.2

theorem shift_resolvent_iff (N : ℕ) (H : System N) (c E : ℝ) :
    OperatorModel.ResolventAt (shiftOperator N H c) (E + c) ↔
      OperatorModel.ResolventAt H E := by
  have he (ψ : State N) (hψ : ψ ∈ H.domain) :
      (shiftOperator N H c).map ⟨ψ, hψ⟩ - (E + c) • ψ = H.map ⟨ψ, hψ⟩ - E • ψ := by
    change H.map ⟨ψ, hψ⟩ + c • ψ - (E + c) • ψ = _
    rw [add_smul]
    abel
  constructor
  · rintro ⟨R, hd, hl, hr⟩
    refine ⟨R, hd, ?_, ?_⟩
    · intro f hf
      simpa only [he] using hl f hf
    · intro ψ hψ
      simpa only [he] using hr ψ hψ
  · rintro ⟨R, hd, hl, hr⟩
    refine ⟨R, hd, ?_, ?_⟩
    · intro f hf
      exact (he (R f) hf).trans (hl f hf)
    · intro ψ hψ
      exact (congrArg R (he ψ hψ)).trans (hr ψ hψ)

theorem shift_spectrum_iff (N : ℕ) (H : System N) (c E : ℝ) :
    E + c ∈ OperatorModel.spectrum (shiftOperator N H c) ↔
      E ∈ OperatorModel.spectrum H := not_congr (shift_resolvent_iff N H c E)

theorem shift_eigenspace (N : ℕ) (H : System N) (c E : ℝ) :
    OperatorModel.eigenspace (shiftOperator N H c) (E + c) =
      OperatorModel.eigenspace H E := by
  unfold OperatorModel.eigenspace
  congr 1
  ext ψ
  constructor
  · rintro ⟨hd, he⟩
    refine ⟨hd, ?_⟩
    change H.map ⟨ψ, hd⟩ + c • ψ = (E + c) • ψ at he
    rw [add_smul] at he
    exact add_right_cancel he
  · rintro ⟨hd, he⟩
    refine ⟨hd, ?_⟩
    change H.map ⟨ψ, hd⟩ + c • ψ = (E + c) • ψ
    rw [he, add_smul]

theorem shift_multiplicity (N : ℕ) (H : System N) (c E : ℝ) :
    OperatorModel.multiplicity (shiftOperator N H c) (E + c) =
      OperatorModel.multiplicity H E := by
  unfold OperatorModel.multiplicity
  rw [shift_eigenspace]

theorem shift_ground (N : ℕ) (H : System N) (c E : ℝ) (ψ : State N)
    (hψ : GroundState N H E ψ) : GroundState N (shiftOperator N H c) (E + c) ψ := by
  refine ⟨(shift_eigen_iff N H c E ψ).mpr hψ.1, ?_, ?_⟩
  · intro e he
    have hm : e - c ∈ OperatorModel.spectrum H := by
      apply (shift_spectrum_iff N H c (e - c)).mp
      simpa only [sub_add_cancel] using he
    have := hψ.2.1 (e - c) hm
    linarith
  · rw [shift_multiplicity]
    exact hψ.2.2

theorem shift_selfAdjoint (N : ℕ) (H : System N) (c : ℝ)
    (hH : OperatorModel.SelfAdjoint H) : OperatorModel.SelfAdjoint (shiftOperator N H c) := by
  refine ⟨hH.1, hH.2.1, ?_, ?_⟩
  · intro z ψ hψ hz
    change H.map ⟨z • ψ, hz⟩ + c • (z • ψ) = z • (H.map ⟨ψ, hψ⟩ + c • ψ)
    rw [hH.2.2.1 z ψ hψ hz, smul_add, smul_comm c z]
  · intro ψ f
    have hg : (∃ h : ψ ∈ (shiftOperator N H c).domain,
        (shiftOperator N H c).map ⟨ψ, h⟩ = f) ↔
        ∃ h : ψ ∈ H.domain, H.map ⟨ψ, h⟩ = f - c • ψ := by
      constructor
      · rintro ⟨h, he⟩
        exact ⟨h, (eq_sub_iff_add_eq).mpr he⟩
      · rintro ⟨h, he⟩
        exact ⟨h, (eq_sub_iff_add_eq).mp he⟩
    rw [hg, hH.2.2.2 ψ (f - c • ψ)]
    apply forall_congr'
    intro η
    apply forall_congr'
    intro hη
    change inner ℂ (H.map ⟨η, hη⟩) ψ = inner ℂ η (f - c • ψ) ↔
      inner ℂ (H.map ⟨η, hη⟩ + c • η) ψ = inner ℂ η f
    simp_rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rw [inner_sub_right, inner_add_left, inner_smul_real_left, inner_smul_real_right]
    exact eq_sub_iff_add_eq

theorem shift_facts (N : ℕ) (H : System N) (A : Point → Point)
    (V : Configuration N → ℝ) (b c : ℝ) (hH : Facts N H A V b) :
    Facts N (shiftOperator N H c) A (fun x => V x + c) (b - c) := by
  have hv : (fun x => V x + c + (b - c)) = fun x => V x + b := by
    funext x
    ring
  have hvx (x : Configuration N) : V x + c + (b - c) = V x + b := by ring
  refine ⟨shift_selfAdjoint N H c hH.1, ?_, ?_, ?_⟩
  · simpa only [hvx] using hH.2.1
  · simpa only [hv] using hH.2.2.1
  · intro ψ η
    have hg : (∃ h : ψ ∈ (shiftOperator N H c).domain,
        (shiftOperator N H c).map ⟨ψ, h⟩ = η) ↔
        ∃ h : ψ ∈ H.domain, H.map ⟨ψ, h⟩ = η - c • ψ := by
      constructor
      · rintro ⟨h, he⟩
        exact ⟨h, (eq_sub_iff_add_eq).mpr he⟩
      · rintro ⟨h, he⟩
        exact ⟨h, (eq_sub_iff_add_eq).mp he⟩
    rw [hg, hH.2.2.2 ψ (η - c • ψ), hv]
    have he : η - c • ψ + b • ψ = η + (b - c) • ψ := by
      rw [sub_smul]
      abel
    rw [he]

theorem hamiltonian_shift (N : ℕ) (H : System N) (A : Point → Point)
    (v : Point → ℝ) (κ b c E : ℝ) (ψ : State N)
    (hH : Facts N H A (hamiltonianPotential N v κ) b)
    (hψ : GroundState N H E ψ) :
    Facts N (shiftOperator N H (N * c)) A
      (hamiltonianPotential N (fun x => v x + c) κ) (b - N * c) ∧
    GroundState N (shiftOperator N H (N * c)) (E + N * c) ψ := by
  rw [hamiltonianPotential_shift]
  exact ⟨shift_facts N H A _ b (N * c) hH, shift_ground N H (N * c) E ψ hψ⟩

theorem form_shift (N : ℕ) (A : Point → Point) (V : Configuration N → ℝ)
    (f g : Configuration N → ℂ) (c : ℝ)
    (hform : Integrable (fun x =>
      (∑ i : Fin N, ∑ k : Fin 3, conj (momentum N A f i k x) * momentum N A g i k x) +
        (V x : ℂ) * conj (f x) * g x))
    (hprod : Integrable (fun x => conj (f x) * g x)) :
    form N A (fun x => V x + c) f g = form N A V f g + (c : ℂ) * ∫ x, conj (f x) * g x := by
  have he (x : Configuration N) :
      (∑ i : Fin N, ∑ k : Fin 3, conj (momentum N A f i k x) * momentum N A g i k x) +
        ((V x + c : ℝ) : ℂ) * conj (f x) * g x =
      ((∑ i : Fin N, ∑ k : Fin 3, conj (momentum N A f i k x) * momentum N A g i k x) +
        (V x : ℂ) * conj (f x) * g x) + (c : ℂ) * (conj (f x) * g x) := by
    push_cast
    ring
  unfold form
  simp_rw [he]
  rw [integral_add hform (hprod.const_mul (c : ℂ)), integral_const_mul]

theorem momentum_paramagnetic (N : ℕ) (A : Point → Point)
    (f : Configuration N → ℂ) (x : Configuration N) (i : Fin N) (k : Fin 3) :
    momentum N A f i k x = momentum N 0 f i k x + (A (x i) k : ℂ) * f x := by
  simp [momentum]

theorem paramagnetic_integrand (N : ℕ) (η : Point → ℝ) (hη : ContDiff ℝ ∞ η)
    (f : Configuration N → ℂ) (hf : Differentiable ℝ f)
    (x : Configuration N) (i : Fin N) (k : Fin 3) :
    (conj (wave N η f x) * momentum N 0 (wave N η f) i k x).re =
      (conj (f x) * momentum N 0 f i k x).re - gradient η (x i) k * Complex.normSq (f x) := by
  have hg := momentum_gauge N η hη (0 : Point → Point) f hf x i k
  simp only [zero_add] at hg
  rw [momentum_paramagnetic] at hg
  have he : conj (wave N η f x) * momentum N 0 (wave N η f) i k x =
      conj (f x) * momentum N 0 f i k x - (gradient η (x i) k : ℂ) * (Complex.normSq (f x) : ℂ) := by
    have hg0 := (eq_sub_iff_add_eq).mpr hg
    rw [hg0, mul_sub]
    have hleft : conj (wave N η f x) * (phase N η x * momentum N 0 f i k x) =
        conj (f x) * momentum N 0 f i k x := by
      dsimp only [wave]
      rw [map_mul]
      calc
        _ = (conj (phase N η x) * phase N η x) *
            (conj (f x) * momentum N 0 f i k x) := by ring
        _ = _ := by rw [phase_conj_mul, one_mul]
    have hright : conj (wave N η f x) * ((gradient η (x i) k : ℂ) * wave N η f x) =
        (gradient η (x i) k : ℂ) * (Complex.normSq (f x) : ℂ) := by
      calc
        _ = (gradient η (x i) k : ℂ) * (conj (wave N η f x) * wave N η f x) := by ring
        _ = (gradient η (x i) k : ℂ) * (Complex.normSq (wave N η f x) : ℂ) := by
          rw [Complex.normSq_eq_conj_mul_self]
        _ = _ := by rw [wave, Complex.normSq_mul, phase_normSq, one_mul]
    rw [hleft, hright]
  rw [he]
  simp

theorem paramagnetic_current_gauge (N : ℕ) (η : Point → ℝ) (hη : ContDiff ℝ ∞ η)
    (f : Configuration (N + 1) → ℂ) (hf : Differentiable ℝ f) (x : Point) (k : Fin 3)
    (hi : Integrable (fun y : Configuration N =>
      (conj (f (Fin.cons x y)) * momentum (N + 1) 0 f 0 k (Fin.cons x y)).re))
    (hn : Integrable (fun y : Configuration N => Complex.normSq (f (Fin.cons x y)))) :
    current N 0 (wave (N + 1) η f) x k =
      current N 0 f x k - density N f x * gradient η x k := by
  unfold current density
  simp_rw [paramagnetic_integrand (N + 1) η hη f hf, Fin.cons_zero]
  rw [integral_sub hi (hn.const_mul _), integral_const_mul]
  ring

end MagHK.GeneralGauge
