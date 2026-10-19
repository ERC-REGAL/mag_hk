import MagHK.OneParticleCurl
import Mathlib.Analysis.Complex.Basic

/-! Assembly of both parts of the manuscript's one-particle proposition.
Only universally quantified standard weak-operator calculus, elliptic
regularity and positive-measure UCP remain as background inputs. -/
noncomputable section
namespace MagHK.OneParticleWeak
open MeasureTheory Set MagHK.WeakDifferential
open scoped ContDiff

def complexWave (u v : Space → ℝ) (x : Space) : ℂ := ⟨u x, v x⟩

theorem density_complex (u v : Space → ℝ) (x : Space) :
    density u v x = Complex.normSq (complexWave u v x) := by
  simp [density, complexWave, Complex.normSq_apply, pow_two]

theorem current_complex (u v : Space → ℝ) (du dv : Index → Space → ℝ)
    (A : Space → Space) (x : Space) (i : Index) :
    current u v du dv A x i =
      (star (complexWave u v x) * complexWave (du i) (dv i) x).im +
        Complex.normSq (complexWave u v x) * A x i := by
  simp [current, complexWave, density, Complex.mul_im, Complex.normSq_apply, pow_two]
  <;> ring

/-- The nonvanishing set used in the weak quotient calculation is exactly
the positive-density region in the submission's proposition. -/
theorem Regularized.omega_eq_positive
    {A : Space → Space} {V : Space → ℝ} {E : ℝ}
    {W : WeakSolution A V E} (R : Regularized W) :
    R.omega = {x | 0 < R.rho x} := by
  ext x
  change R.rho x ≠ 0 ↔ 0 < R.rho x
  have hnonneg : 0 ≤ R.rho x := by
    dsimp [Regularized.rho, density]
    positivity
  exact ⟨fun hx => lt_of_le_of_ne hnonneg hx.symm, ne_of_gt⟩

/-- UCP makes the continuous representative's nodal set closed and null,
and its positive-density region open and dense. It does not make the
wavefunction everywhere nonzero or twice continuously differentiable. -/
theorem one_particle_nodal_set
    (elliptic : StandardEllipticLibrary) (ucp : StandardUCPLibrary)
    (A : Space → Space) (V : Space → ℝ) (E : ℝ)
    (hA : ContDiff ℝ 1 A) (hV : Continuous V)
    (W : WeakSolution A V E) (hn : ¬ (∀ᵐ x, W.u x = 0 ∧ W.v x = 0)) :
    ∃ R : Regularized W,
      IsClosed {x | R.rho x = 0} ∧ volume {x | R.rho x = 0} = 0 ∧
      IsOpen {x | 0 < R.rho x} ∧ Dense {x | 0 < R.rho x} ∧
      (∀ᵐ x, 0 < R.rho x) := by
  obtain ⟨R⟩ := elliptic A V E hA hV W
  have hp : ∀ᵐ x, 0 < R.rho x := by
    filter_upwards [R.rho_rep, ucp A V E hA hV W hn] with x hx hpos
    simpa only [hx] using hpos
  have hz : volume {x | R.rho x = 0} = 0 := by
    have hnz : ∀ᵐ x, R.rho x ≠ 0 := hp.mono (fun _ hx => ne_of_gt hx)
    simpa only [ae_iff, not_not] using hnz
  refine ⟨R, isClosed_eq R.rho_continuous continuous_const, hz, ?_,
    volume.dense_of_ae hp, hp⟩
  rw [← R.omega_eq_positive]
  exact R.omega_open

theorem one_particle_hk
    (L : StandardWeakOperatorLibrary) (elliptic : StandardEllipticLibrary)
    (ucp : StandardUCPLibrary)
    (A₁ A₂ : Space → Space) (V₁ V₂ : Space → ℝ) (E₁ E₂ : ℝ)
    (hA₁ : ContDiff ℝ 1 A₁) (hA₂ : ContDiff ℝ 1 A₂)
    (hV₁ : Continuous V₁) (hV₂ : Continuous V₂)
    (W₁ : WeakSolution A₁ V₁ E₁) (W₂ : WeakSolution A₂ V₂ E₂)
    (hn₁ : ¬ (∀ᵐ x, W₁.u x = 0 ∧ W₁.v x = 0))
    (hn₂ : ¬ (∀ᵐ x, W₂.u x = 0 ∧ W₂.v x = 0))
    (hr : density W₁.u W₁.v =ᵐ[volume] density W₂.u W₂.v)
    (hj : ∀ᵐ x, ∀ i, current W₁.u W₁.v W₁.du W₁.dv A₁ x i =
      current W₂.u W₂.v W₂.du W₂.dv A₂ x i) :
    (∀ x, V₁ x - V₂ x = E₁ - E₂) ∧
      ∃ χ : Space → ℝ, ∀ x, HasGradientAt χ (A₁ x - A₂ x) x := by
  obtain ⟨R₁⟩ := elliptic A₁ V₁ E₁ hA₁ hV₁ W₁
  obtain ⟨R₂⟩ := elliptic A₂ V₂ E₂ hA₂ hV₂ W₂
  have hρ : R₁.rho =ᵐ[volume] R₂.rho := R₁.rho_rep.trans (hr.trans R₂.rho_rep.symm)
  have hJ : ∀ᵐ x, ∀ i, R₁.j x i = R₂.j x i := by
    have hr₁ := ae_all_iff.mpr R₁.j_rep
    have hr₂ := ae_all_iff.mpr R₂.j_rep
    filter_upwards [hr₁, hr₂, hj] with x hx₁ hx₂ hx
    intro i
    exact (hx₁ i).trans ((hx i).trans (hx₂ i).symm)
  have hpos₁ := ucp A₁ V₁ E₁ hA₁ hV₁ W₁ hn₁
  have hpos₂ := ucp A₂ V₂ E₂ hA₂ hV₂ W₂ hn₂
  have hz₁ : ∀ᵐ x, R₁.rho x ≠ 0 := by
    filter_upwards [R₁.rho_rep, hpos₁] with x hx hp
    rw [hx]
    exact ne_of_gt hp
  have hz₂ : ∀ᵐ x, R₂.rho x ≠ 0 := by
    filter_upwards [R₂.rho_rep, hpos₂] with x hx hp
    rw [hx]
    exact ne_of_gt hp
  exact ⟨scalar_uniqueness L R₁ R₂ hV₁ hV₂ hz₂ hρ hJ,
    gradient_difference_of_curl_components A₁ A₂ hA₁ hA₂
      (curl_uniqueness L R₁ R₂ hA₁ hA₂ hz₁ hρ hJ)⟩

/-- The curl identity is stated through actual weak partial derivatives of
j/rho on its nonvanishing open set. The zero-current conclusion is global. -/
theorem one_particle_curl
    (L : StandardWeakOperatorLibrary) (elliptic : StandardEllipticLibrary)
    (ucp : StandardUCPLibrary)
    (A : Space → Space) (V : Space → ℝ) (E : ℝ)
    (hA : ContDiff ℝ 1 A) (hV : Continuous V)
    (W : WeakSolution A V E) (hn : ¬ (∀ᵐ x, W.u x = 0 ∧ W.v x = 0)) :
    (∀ᵐ x, 0 < density W.u W.v x) ∧
    ∃ R : Regularized W, IsOpen R.omega ∧
      (∀ᵐ x, x ∈ R.omega) ∧
      (∀ i j, WeakPartial R.omega (R.velocity j) (R.velocityDerivative i j) i) ∧
      (∀ᵐ x, x ∈ R.omega → ∀ i j,
        R.velocityDerivative i j x - R.velocityDerivative j i x =
          dCoord (fun y => A y j) i x - dCoord (fun y => A y i) j x) ∧
      ((∀ᵐ x, ∀ i, current W.u W.v W.du W.dv A x i = 0) →
        ∀ x, MagHK.Poincare.curl A x = 0) := by
  have hp := ucp A V E hA hV W hn
  obtain ⟨R⟩ := elliptic A V E hA hV W
  have hz : ∀ᵐ x, R.rho x ≠ 0 := by
    filter_upwards [R.rho_rep, hp] with x hx hpx
    rw [hx]
    exact ne_of_gt hpx
  refine ⟨hp, R, R.omega_open, hz, R.velocity_weak L hA, R.velocity_curl, ?_⟩
  intro hj
  have hJ : ∀ᵐ x, ∀ i, R.j x i = 0 := by
    apply ae_all_iff.mpr
    intro i
    exact (R.j_rep i).trans (hj.mono (fun _ hx => hx i))
  exact curl_zero_of_components A (hA.differentiable (by decide))
    (zero_current_curl_components L R hA hz hJ)

end MagHK.OneParticleWeak
