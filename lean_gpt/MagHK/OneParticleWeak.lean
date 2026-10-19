import MagHK.WeakDifferential
import MagHK.OneParticle

/-!
The one-particle proposition for literal weak magnetic equations. Background
inputs are stated universally as local closed-derivative operator laws,
elliptic regularity and positive-measure unique continuation. Neither potential
reconstruction nor current rigidity is an input to any of these libraries.
-/
noncomputable section
namespace MagHK.OneParticleWeak
open MeasureTheory Set MagHK.WeakDifferential
open scoped ContDiff BigOperators

def density (u v : Space → ℝ) (x : Space) : ℝ := u x ^ 2 + v x ^ 2

def current (u v : Space → ℝ) (du dv : Index → Space → ℝ)
    (A : Space → Space) (x : Space) (i : Index) : ℝ :=
  u x * dv i x - v x * du i x + density u v x * A x i

def divergence (A : Space → Space) (x : Space) : ℝ :=
  ∑ i : Index, dCoord (fun y => A y i) i x

def LocalL2 (f : Space → ℝ) : Prop :=
  ∀ R : ℝ, 0 < R → MemLp f 2 (volume.restrict (Metric.ball (0 : Space) R))

/-- H1_loc real and imaginary parts, with their actual distributional first
partials and the real and imaginary magnetic weak equations. -/
structure WeakSolution (A : Space → Space) (V : Space → ℝ) (E : ℝ) where
  u : Space → ℝ
  v : Space → ℝ
  du : Index → Space → ℝ
  dv : Index → Space → ℝ
  u_l2 : LocalL2 u
  v_l2 : LocalL2 v
  du_l2 : ∀ i, LocalL2 (du i)
  dv_l2 : ∀ i, LocalL2 (dv i)
  du_weak : ∀ i, WeakPartial univ u (du i) i
  dv_weak : ∀ i, WeakPartial univ v (dv i) i
  real_equation : ∀ η : Space → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
    (∫ x, ∑ i, du i x * dCoord η i x) +
      (∫ x, (2 * ∑ i, A x i * dv i x) * η x +
        (divergence A x * v x + ((∑ i, (A x i) ^ 2) + V x - E) * u x) * η x) = 0
  imag_equation : ∀ η : Space → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
    (∫ x, ∑ i, dv i x * dCoord η i x) +
      (∫ x, (-2 * ∑ i, A x i * du i x) * η x +
        (-divergence A x * u x + ((∑ i, (A x i) ^ 2) + V x - E) * v x) * η x) = 0

/-- Actual C1 representatives and weak Hessians furnished by elliptic
regularity. The Hessian is not presumed to be a continuous classical derivative. -/
structure Regularized {A : Space → Space} {V : Space → ℝ} {E : ℝ}
    (W : WeakSolution A V E) where
  u : Space → ℝ
  v : Space → ℝ
  Hu : Index → Index → Space → ℝ
  Hv : Index → Index → Space → ℝ
  u_c1 : ContDiff ℝ 1 u
  v_c1 : ContDiff ℝ 1 v
  u_rep : u =ᵐ[volume] W.u
  v_rep : v =ᵐ[volume] W.v
  du_rep : ∀ i, dCoord u i =ᵐ[volume] W.du i
  dv_rep : ∀ i, dCoord v i =ᵐ[volume] W.dv i
  Hu_weak : ∀ i j, WeakPartial univ (dCoord u j) (Hu i j) i
  Hv_weak : ∀ i j, WeakPartial univ (dCoord v j) (Hv i j) i
  Hu_symm : ∀ᵐ x, ∀ i j, Hu i j x = Hu j i x
  Hv_symm : ∀ᵐ x, ∀ i j, Hv i j x = Hv j i x
  real_equation : ∀ᵐ x, -(∑ i, Hu i i x) +
    2 * ∑ i, A x i * dCoord v i x + divergence A x * v x +
    ((∑ i, (A x i) ^ 2) + V x - E) * u x = 0
  imag_equation : ∀ᵐ x, -(∑ i, Hv i i x) -
    2 * ∑ i, A x i * dCoord u i x - divergence A x * u x +
    ((∑ i, (A x i) ^ 2) + V x - E) * v x = 0

/-- The usual H1_loc to W2,p_loc and C1 bootstrap for locally bounded
magnetic coefficients. It asserts regularity and the PDE, never reconstruction. -/
def StandardEllipticLibrary : Prop :=
  ∀ (A : Space → Space) (V : Space → ℝ) (E : ℝ),
    ContDiff ℝ 1 A → Continuous V → ∀ W : WeakSolution A V E, Nonempty (Regularized W)

/-- Positive-measure UCP, specialized only by the explicit coefficient
hypotheses of the proposition. Nonzero means nonzero as a measurable class. -/
def StandardUCPLibrary : Prop :=
  ∀ (A : Space → Space) (V : Space → ℝ) (E : ℝ),
    ContDiff ℝ 1 A → Continuous V → ∀ W : WeakSolution A V E,
    (¬ (∀ᵐ x, W.u x = 0 ∧ W.v x = 0)) → ∀ᵐ x, 0 < density W.u W.v x

variable {A : Space → Space} {V : Space → ℝ} {E : ℝ}
  {W : WeakSolution A V E}

def Regularized.rho (R : Regularized W) := density R.u R.v

def Regularized.j (R : Regularized W) := current R.u R.v (dCoord R.u) (dCoord R.v) A

def Regularized.rhoGrad (R : Regularized W) (i : Index) (x : Space) : ℝ :=
  2 * (R.u x * dCoord R.u i x + R.v x * dCoord R.v i x)

def Regularized.rhoHess (R : Regularized W) (i j : Index) (x : Space) : ℝ :=
  2 * (dCoord R.u i x * dCoord R.u j x + R.u x * R.Hu i j x +
    dCoord R.v i x * dCoord R.v j x + R.v x * R.Hv i j x)

def Regularized.lapRho (R : Regularized W) (x : Space) : ℝ := ∑ i, R.rhoHess i i x

def Regularized.omega (R : Regularized W) : Set Space := {x | R.rho x ≠ 0}

theorem Regularized.rho_continuous (R : Regularized W) : Continuous R.rho :=
  (R.u_c1.continuous.pow 2).add (R.v_c1.continuous.pow 2)

theorem Regularized.omega_open (R : Regularized W) : IsOpen R.omega :=
  isOpen_ne_fun R.rho_continuous continuous_const

theorem Regularized.rho_rep (R : Regularized W) : R.rho =ᵐ[volume] density W.u W.v := by
  filter_upwards [R.u_rep, R.v_rep] with x hu hv
  simp [Regularized.rho, density, hu, hv]

theorem Regularized.j_rep (R : Regularized W) (i : Index) :
    (fun x => R.j x i) =ᵐ[volume] (fun x => current W.u W.v W.du W.dv A x i) := by
  filter_upwards [R.u_rep, R.v_rep, R.du_rep i, R.dv_rep i] with x hu hv hdu hdv
  simp [Regularized.j, current, density, hu, hv, hdu, hdv]

theorem Regularized.j_continuous (R : Regularized W) (hA : Continuous A) (i : Index) :
    Continuous (fun x => R.j x i) := by
  exact ((R.u_c1.continuous.mul (partial_continuous R.v R.v_c1 i)).sub
    (R.v_c1.continuous.mul (partial_continuous R.u R.u_c1 i))).add
    (R.rho_continuous.mul ((PiLp.continuous_apply 2 (fun _ : Index => ℝ) i).comp hA))

theorem Regularized.rhoGrad_weak (L : StandardWeakOperatorLibrary)
    (R : Regularized W) (i : Index) : WeakPartial univ R.rho (R.rhoGrad i) i := by
  have hu := L.multiply univ isOpen_univ R.u R.u (dCoord R.u i) i R.u_c1.contDiffOn
    (L.classical univ isOpen_univ R.u R.u_c1.contDiffOn i)
  have hv := L.multiply univ isOpen_univ R.v R.v (dCoord R.v i) i R.v_c1.contDiffOn
    (L.classical univ isOpen_univ R.v R.v_c1.contDiffOn i)
  exact (L.add isOpen_univ hu hv).congr
    (by funext x; dsimp [Regularized.rho, density]; ring)
    (by funext x; dsimp [Regularized.rhoGrad]; ring)

theorem Regularized.rhoHess_weak (L : StandardWeakOperatorLibrary)
    (R : Regularized W) (i j : Index) :
    WeakPartial univ (R.rhoGrad j) (R.rhoHess i j) i := by
  have hu := L.multiply univ isOpen_univ R.u (dCoord R.u j) (R.Hu i j) i
    R.u_c1.contDiffOn (R.Hu_weak i j)
  have hv := L.multiply univ isOpen_univ R.v (dCoord R.v j) (R.Hv i j) i
    R.v_c1.contDiffOn (R.Hv_weak i j)
  exact (L.scale isOpen_univ (L.add isOpen_univ hu hv) 2).congr rfl
    (by funext x; dsimp [Regularized.rhoHess]; ring)

/-- The scalar reconstruction formula now follows from the literal PDE and
literal weak derivatives, rather than independently supplied derivative jets. -/
theorem Regularized.scalar_reconstruction (R : Regularized W) :
    ∀ᵐ x, R.rho x ^ 2 * (V x - E) = R.rho x * R.lapRho x / 2 -
      (∑ i, R.rhoGrad i x ^ 2) / 4 - ∑ i, R.j x i ^ 2 := by
  filter_upwards [R.real_equation, R.imag_equation] with x hre him
  have h := MagHK.OneParticle.scalar_reconstruction
    (R.u x) (R.v x) (∑ i, R.Hu i i x) (∑ i, R.Hv i i x)
    (divergence A x) (V x) E (fun i => dCoord R.u i x) (fun i => dCoord R.v i x)
    (fun i => A x i) hre him
  have hlap : R.lapRho x = 2 * ((∑ i, ((dCoord R.u i x)^2 + (dCoord R.v i x)^2)) +
      R.u x * (∑ i, R.Hu i i x) + R.v x * (∑ i, R.Hv i i x)) := by
    calc
      R.lapRho x = ∑ i, 2 * (((dCoord R.u i x)^2 + (dCoord R.v i x)^2) +
          R.u x * R.Hu i i x + R.v x * R.Hv i i x) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [Regularized.rhoHess]
        ring
      _ = _ := by
        rw [← Finset.mul_sum]
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hgrad : (∑ i, R.rhoGrad i x ^ 2) =
      4 * ∑ i, (R.u x * dCoord R.u i x + R.v x * dCoord R.v i x)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [Regularized.rhoGrad]
    ring
  rw [hlap, hgrad]
  dsimp [Regularized.rho, density, Regularized.j, current] at *
  linear_combination h


variable {A₁ A₂ : Space → Space} {V₁ V₂ : Space → ℝ} {E₁ E₂ : ℝ}
  {W₁ : WeakSolution A₁ V₁ E₁} {W₂ : WeakSolution A₂ V₂ E₂}

theorem equal_density_derivatives (L : StandardWeakOperatorLibrary)
    (R₁ : Regularized W₁) (R₂ : Regularized W₂)
    (hr : R₁.rho =ᵐ[volume] R₂.rho) :
    (∀ᵐ x, ∀ i, R₁.rhoGrad i x = R₂.rhoGrad i x) ∧
    R₁.lapRho =ᵐ[volume] R₂.lapRho := by
  have hg (i : Index) : R₁.rhoGrad i =ᵐ[volume] R₂.rhoGrad i := by
    have h := L.unique univ isOpen_univ _ _ _ _ i (R₁.rhoGrad_weak L i)
      (R₂.rhoGrad_weak L i) (hr.mono (fun x hx _ => hx))
    exact h.mono (fun x hx => hx (mem_univ x))
  have hh (i : Index) : R₁.rhoHess i i =ᵐ[volume] R₂.rhoHess i i := by
    have h := L.unique univ isOpen_univ _ _ _ _ i (R₁.rhoHess_weak L i i)
      (R₂.rhoHess_weak L i i) ((hg i).mono (fun x hx _ => hx))
    exact h.mono (fun x hx => hx (mem_univ x))
  refine ⟨ae_all_iff.mpr hg, ?_⟩
  filter_upwards [ae_all_iff.mpr hh] with x hx
  exact Finset.sum_congr rfl (fun i _ => hx i)

theorem scalar_uniqueness (L : StandardWeakOperatorLibrary)
    (R₁ : Regularized W₁) (R₂ : Regularized W₂)
    (hV₁ : Continuous V₁) (hV₂ : Continuous V₂)
    (hnz : ∀ᵐ x, R₂.rho x ≠ 0) (hr : R₁.rho =ᵐ[volume] R₂.rho)
    (hj : ∀ᵐ x, ∀ i, R₁.j x i = R₂.j x i) :
    ∀ x, V₁ x - V₂ x = E₁ - E₂ := by
  obtain ⟨hg, hl⟩ := equal_density_derivatives L R₁ R₂ hr
  have he : (fun x => V₁ x - V₂ x) =ᵐ[volume] (fun _ => E₁ - E₂) := by
    filter_upwards [R₁.scalar_reconstruction, R₂.scalar_reconstruction, hr, hg, hl, hj, hnz]
      with x h₁ h₂ hx hgx hlx hjx hnzx
    have hgs : (∑ i, R₁.rhoGrad i x ^ 2) = ∑ i, R₂.rhoGrad i x ^ 2 :=
      Finset.sum_congr rfl (fun i _ => congrArg (fun r : ℝ => r^2) (hgx i))
    have hjs : (∑ i, R₁.j x i ^ 2) = ∑ i, R₂.j x i ^ 2 :=
      Finset.sum_congr rfl (fun i _ => congrArg (fun r : ℝ => r^2) (hjx i))
    rw [hx, hlx, hgs, hjs] at h₁
    exact MagHK.OneParticle.equal_reconstructed_potentials _ _ _ _ _ _ _ _ hnzx h₁ h₂
  exact fun x => congrFun (Measure.eq_of_ae_eq he (hV₁.sub hV₂) continuous_const) x

end MagHK.OneParticleWeak
