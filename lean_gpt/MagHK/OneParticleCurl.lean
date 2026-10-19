import MagHK.OneParticleWeak

/-! Weak-curl reconstruction on the nonvanishing set. All coefficients in
its quotient rule are literal functions. The Hessians are weak derivatives,
so no C2 regularity of the wavefunction is imposed. -/
noncomputable section
namespace MagHK.OneParticleWeak
open MeasureTheory Set MagHK.WeakDifferential
open scoped ContDiff BigOperators
variable {A : Space → Space} {V : Space → ℝ} {E : ℝ}
  {W : WeakSolution A V E}

theorem component_c1 (A : Space → Space) (hA : ContDiff ℝ 1 A) (i : Index) :
    ContDiff ℝ 1 (fun x => A x i) := by
  have hp : ContDiff ℝ 1 (PiLp.proj 2 (fun _ : Index => ℝ) i : Space →L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff _
  exact hp.comp hA

theorem dCoord_component (A : Space → Space) (hA : Differentiable ℝ A)
    (i j : Index) (x : Space) :
    dCoord (fun y => A y j) i x =
      (fderiv ℝ A x (EuclideanSpace.single i 1)) j := by
  have h := ((PiLp.proj 2 (fun _ : Index => ℝ) j).hasFDerivAt.comp x (hA x).hasFDerivAt).fderiv
  exact congrArg (fun T : Space →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) h

theorem Regularized.rho_c1 (R : Regularized W) : ContDiff ℝ 1 R.rho :=
  (R.u_c1.pow 2).add (R.v_c1.pow 2)

theorem Regularized.dCoord_rho (R : Regularized W) (i : Index) (x : Space) :
    dCoord R.rho i x = R.rhoGrad i x := by
  have hu := R.u_c1.differentiable (by decide)
  have hv := R.v_c1.differentiable (by decide)
  have hr : R.rho = fun y => R.u y * R.u y + R.v y * R.v y := by
    funext y
    simp only [Regularized.rho, density, pow_two]
  rw [hr, partial_add _ _ (show Differentiable ℝ (fun y => R.u y * R.u y) from hu.mul hu)
    (show Differentiable ℝ (fun y => R.v y * R.v y) from hv.mul hv), dCoord_mul _ _ (hu x) (hu x),
    dCoord_mul _ _ (hv x) (hv x)]
  dsimp [Regularized.rhoGrad]
  ring

def Regularized.coeffU (R : Regularized W) (x : Space) : ℝ := R.u x / R.rho x

def Regularized.coeffV (R : Regularized W) (x : Space) : ℝ := R.v x / R.rho x

def Regularized.velocity (R : Regularized W) (j : Index) (x : Space) : ℝ := R.j x j / R.rho x

def Regularized.velocityDerivative (R : Regularized W) (i j : Index) (x : Space) : ℝ :=
  dCoord R.coeffU i x * dCoord R.v j x + R.coeffU x * R.Hv i j x -
    (dCoord R.coeffV i x * dCoord R.u j x + R.coeffV x * R.Hu i j x) +
    dCoord (fun y => A y j) i x

theorem Regularized.coeffU_c1 (R : Regularized W) : ContDiffOn ℝ 1 R.coeffU R.omega :=
  R.u_c1.contDiffOn.div R.rho_c1.contDiffOn (fun _ hx => hx)

theorem Regularized.coeffV_c1 (R : Regularized W) : ContDiffOn ℝ 1 R.coeffV R.omega :=
  R.v_c1.contDiffOn.div R.rho_c1.contDiffOn (fun _ hx => hx)

theorem Regularized.velocity_weak (L : StandardWeakOperatorLibrary)
    (R : Regularized W) (hA : ContDiff ℝ 1 A) (i j : Index) :
    WeakPartial R.omega (R.velocity j) (R.velocityDerivative i j) i := by
  have hu := L.restrict univ R.omega isOpen_univ R.omega_open (subset_univ _) _ _ i (R.Hu_weak i j)
  have hv := L.restrict univ R.omega isOpen_univ R.omega_open (subset_univ _) _ _ i (R.Hv_weak i j)
  have hcu := L.multiply R.omega R.omega_open _ _ _ i R.coeffU_c1 hv
  have hcv := L.multiply R.omega R.omega_open _ _ _ i R.coeffV_c1 hu
  have ha := L.classical R.omega R.omega_open _ (component_c1 A hA j).contDiffOn i
  have h := L.add R.omega_open (L.sub R.omega_open hcu hcv) ha
  apply L.congr_ae R.omega R.omega_open _ _ _ _ i h
  · filter_upwards [] with x hx
    change R.u x / R.rho x * dCoord R.v j x - R.v x / R.rho x * dCoord R.u j x + A x j = _
    dsimp [Regularized.velocity, Regularized.j, current]
    change _ = (R.u x * dCoord R.v j x - R.v x * dCoord R.u j x + R.rho x * A x j) / R.rho x
    have hn : R.rho x ≠ 0 := hx
    field_simp
    <;> ring
  · exact ae_of_all _ (fun _ _ => rfl)

/-- Tensor form of the weak curl identity on the nonvanishing open set. -/
theorem Regularized.velocity_curl (R : Regularized W) :
    ∀ᵐ x, x ∈ R.omega → ∀ i j,
      R.velocityDerivative i j x - R.velocityDerivative j i x =
        dCoord (fun y => A y j) i x - dCoord (fun y => A y i) j x := by
  filter_upwards [R.Hu_symm, R.Hv_symm] with x hsu hsv hx i j
  have hn : R.rho x ≠ 0 := hx
  have hu := R.u_c1.differentiable (by decide)
  have hv := R.v_c1.differentiable (by decide)
  have hr := R.rho_c1.differentiable (by decide)
  have hcu (k : Index) : dCoord R.coeffU k x =
      (dCoord R.u k x * R.rho x - R.u x * R.rhoGrad k x) / R.rho x ^ 2 := by
    exact (dCoord_div R.u R.rho (hu x) (hr x) hn k).trans (by rw [R.dCoord_rho])
  have hcv (k : Index) : dCoord R.coeffV k x =
      (dCoord R.v k x * R.rho x - R.v x * R.rhoGrad k x) / R.rho x ^ 2 := by
    exact (dCoord_div R.v R.rho (hv x) (hr x) hn k).trans (by rw [R.dCoord_rho])
  dsimp only [Regularized.velocityDerivative]
  rw [hcu i, hcu j, hcv i, hcv j, hsu i j, hsv i j]
  dsimp only [Regularized.coeffU, Regularized.coeffV]
  field_simp
  dsimp only [Regularized.rho, density, Regularized.rhoGrad]
  ring

variable {A₁ A₂ : Space → Space} {V₁ V₂ : Space → ℝ} {E₁ E₂ : ℝ}
  {W₁ : WeakSolution A₁ V₁ E₁} {W₂ : WeakSolution A₂ V₂ E₂}

theorem curl_uniqueness (L : StandardWeakOperatorLibrary)
    (R₁ : Regularized W₁) (R₂ : Regularized W₂)
    (hA₁ : ContDiff ℝ 1 A₁) (hA₂ : ContDiff ℝ 1 A₂)
    (hnz : ∀ᵐ x, R₁.rho x ≠ 0) (hr : R₁.rho =ᵐ[volume] R₂.rho)
    (hj : ∀ᵐ x, ∀ i, R₁.j x i = R₂.j x i) :
    ∀ x i j, dCoord (fun y => A₁ y j) i x - dCoord (fun y => A₁ y i) j x =
      dCoord (fun y => A₂ y j) i x - dCoord (fun y => A₂ y i) j x := by
  have hrfun : R₁.rho = R₂.rho := Measure.eq_of_ae_eq hr R₁.rho_continuous R₂.rho_continuous
  have ho : R₁.omega = R₂.omega := by simp only [Regularized.omega, hrfun]
  have hd (i j : Index) : ∀ᵐ x, x ∈ R₁.omega →
      R₁.velocityDerivative i j x = R₂.velocityDerivative i j x := by
    have h₂ : WeakPartial R₁.omega (R₂.velocity j) (R₂.velocityDerivative i j) i := by
      rw [ho]
      exact R₂.velocity_weak L hA₂ i j
    apply L.unique R₁.omega R₁.omega_open _ _ _ _ i (R₁.velocity_weak L hA₁ i j) h₂
    filter_upwards [hj] with x hx _
    simp only [Regularized.velocity, hrfun, hx j]
  intro x i j
  have he : (fun x => dCoord (fun y => A₁ y j) i x - dCoord (fun y => A₁ y i) j x) =ᵐ[volume]
      (fun x => dCoord (fun y => A₂ y j) i x - dCoord (fun y => A₂ y i) j x) := by
    filter_upwards [R₁.velocity_curl, R₂.velocity_curl, hd i j, hd j i, hnz]
      with y hc₁ hc₂ hdij hdji hny
    have hy₁ : y ∈ R₁.omega := hny
    have hy₂ : y ∈ R₂.omega := by rw [← ho]; exact hy₁
    rw [← hc₁ hy₁ i j, ← hc₂ hy₂ i j, hdij hy₁, hdji hy₁]
  exact congrFun (Measure.eq_of_ae_eq he
    ((partial_continuous _ (component_c1 A₁ hA₁ j) i).sub
      (partial_continuous _ (component_c1 A₁ hA₁ i) j))
    ((partial_continuous _ (component_c1 A₂ hA₂ j) i).sub
      (partial_continuous _ (component_c1 A₂ hA₂ i) j))) x

theorem gradient_difference_of_curl_components
    (A₁ A₂ : Space → Space) (hA₁ : ContDiff ℝ 1 A₁) (hA₂ : ContDiff ℝ 1 A₂)
    (hcurl : ∀ x i j, dCoord (fun y => A₁ y j) i x - dCoord (fun y => A₁ y i) j x =
      dCoord (fun y => A₂ y j) i x - dCoord (fun y => A₂ y i) j x) :
    ∃ χ : Space → ℝ, ∀ x, HasGradientAt χ (A₁ x - A₂ x) x := by
  have ha₁ := hA₁.differentiable (by decide)
  have ha₂ := hA₂.differentiable (by decide)
  refine ⟨MagHK.Poincare.vectorPotential (fun x => A₁ x - A₂ x), fun x => ?_⟩
  apply MagHK.Poincare.vectorPotential_hasGradientAt _ (ha₁.sub ha₂)
  intro y u v
  apply MagHK.Poincare.inner_symmetric_of_coordinates
  intro i j
  have hc := hcurl y i j
  rw [dCoord_component A₁ ha₁ i j y, dCoord_component A₁ ha₁ j i y,
    dCoord_component A₂ ha₂ i j y, dCoord_component A₂ ha₂ j i y] at hc
  change ((fderiv ℝ (A₁ - A₂) y) (EuclideanSpace.single i 1)) j =
    ((fderiv ℝ (A₁ - A₂) y) (EuclideanSpace.single j 1)) i
  rw [fderiv_sub (ha₁ y) (ha₂ y)]
  change (fderiv ℝ A₁ y (EuclideanSpace.single i 1)) j -
    (fderiv ℝ A₂ y (EuclideanSpace.single i 1)) j =
    (fderiv ℝ A₁ y (EuclideanSpace.single j 1)) i -
    (fderiv ℝ A₂ y (EuclideanSpace.single j 1)) i
  linarith


theorem zero_current_curl_components (L : StandardWeakOperatorLibrary)
    (R : Regularized W) (hA : ContDiff ℝ 1 A)
    (hnz : ∀ᵐ x, R.rho x ≠ 0) (hj : ∀ᵐ x, ∀ i, R.j x i = 0) :
    ∀ x i j, dCoord (fun y => A y j) i x - dCoord (fun y => A y i) j x = 0 := by
  have hd (i j : Index) : ∀ᵐ x, x ∈ R.omega → R.velocityDerivative i j x = 0 := by
    have hz : WeakPartial R.omega (fun _ => 0) (fun _ => 0) i := by
      have hc := L.classical R.omega R.omega_open (fun _ => 0) contDiffOn_const i
      have he : dCoord (fun _ : Space => (0 : ℝ)) i = fun _ => 0 := by
        funext x
        simp [dCoord, fderiv_const]
      rw [he] at hc
      exact hc
    apply L.unique R.omega R.omega_open _ _ _ _ i (R.velocity_weak L hA i j) hz
    filter_upwards [hj] with x hx _
    simp only [Regularized.velocity, hx j, zero_div]
  intro x i j
  have he : (fun x => dCoord (fun y => A y j) i x - dCoord (fun y => A y i) j x) =ᵐ[volume]
      (fun _ => 0) := by
    filter_upwards [R.velocity_curl, hd i j, hd j i, hnz] with y hcy hdij hdji hny
    have hy : y ∈ R.omega := hny
    rw [← hcy hy i j, hdij hy, hdji hy, sub_self]
  exact congrFun (Measure.eq_of_ae_eq he
    ((partial_continuous _ (component_c1 A hA j) i).sub
      (partial_continuous _ (component_c1 A hA i) j)) continuous_const) x

theorem curl_zero_of_components (A : Space → Space) (hA : Differentiable ℝ A)
    (h : ∀ x i j, dCoord (fun y => A y j) i x - dCoord (fun y => A y i) j x = 0) :
    ∀ x, MagHK.Poincare.curl A x = 0 := by
  intro x
  have h12 := h x 1 2
  have h20 := h x 2 0
  have h01 := h x 0 1
  simp only [dCoord_component A hA] at h12 h20 h01
  funext k
  fin_cases k <;> simp [MagHK.Poincare.curl, h12, h20, h01]

end MagHK.OneParticleWeak
