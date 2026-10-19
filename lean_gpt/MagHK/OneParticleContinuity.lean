import MagHK.OneParticleTheorem

/-! The stationary continuity equation used in the one-particle proof,
with actual weak derivatives of the literal current. -/
noncomputable section
namespace MagHK.OneParticleWeak
open MeasureTheory Set MagHK.WeakDifferential
open scoped ContDiff BigOperators
variable {A : Space → Space} {V : Space → ℝ} {E : ℝ}
  {W : WeakSolution A V E}

def Regularized.currentDerivative (R : Regularized W) (i j : Index) (x : Space) : ℝ :=
  dCoord R.u i x * dCoord R.v j x + R.u x * R.Hv i j x -
    (dCoord R.v i x * dCoord R.u j x + R.v x * R.Hu i j x) +
    dCoord (fun y => A y j) i x * R.rho x + A x j * R.rhoGrad i x

theorem Regularized.current_weak (L : StandardWeakOperatorLibrary)
    (R : Regularized W) (hA : ContDiff ℝ 1 A) (i j : Index) :
    WeakPartial univ (fun x => R.j x j) (R.currentDerivative i j) i := by
  have hu := L.multiply univ isOpen_univ _ _ _ i R.u_c1.contDiffOn (R.Hv_weak i j)
  have hv := L.multiply univ isOpen_univ _ _ _ i R.v_c1.contDiffOn (R.Hu_weak i j)
  have ha := L.multiply univ isOpen_univ _ _ _ i (component_c1 A hA j).contDiffOn
    (R.rhoGrad_weak L i)
  exact (L.add isOpen_univ (L.sub isOpen_univ hu hv) ha).congr
    (by funext x; dsimp [Regularized.j, current, Regularized.rho]; ring)
    (by funext x; dsimp [Regularized.currentDerivative]; ring)

theorem Regularized.current_divergence_zero (R : Regularized W) :
    ∀ᵐ x, (∑ i, R.currentDerivative i i x) = 0 := by
  filter_upwards [R.real_equation, R.imag_equation] with x hre him
  have hd : (∑ i, R.currentDerivative i i x) =
      R.u x * (∑ i, R.Hv i i x) - R.v x * (∑ i, R.Hu i i x) +
      divergence A x * R.rho x +
      2 * (R.u x * (∑ i, A x i * dCoord R.u i x) +
        R.v x * (∑ i, A x i * dCoord R.v i x)) := by
    calc
      (∑ i, R.currentDerivative i i x) = ∑ i,
          (R.u x * R.Hv i i x - R.v x * R.Hu i i x +
            dCoord (fun y => A y i) i x * R.rho x +
            2 * (R.u x * (A x i * dCoord R.u i x) +
              R.v x * (A x i * dCoord R.v i x))) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [Regularized.currentDerivative, Regularized.rhoGrad]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul, divergence]
  rw [hd]
  dsimp only [Regularized.rho, density]
  linear_combination R.v x * hre - R.u x * him

/-- Every weak solution in the proposition has a representative whose
literal current has locally integrable weak derivatives and zero divergence. -/
theorem one_particle_continuity
    (L : StandardWeakOperatorLibrary) (elliptic : StandardEllipticLibrary)
    (A : Space → Space) (V : Space → ℝ) (E : ℝ)
    (hA : ContDiff ℝ 1 A) (hV : Continuous V) (W : WeakSolution A V E) :
    ∃ R : Regularized W,
      (∀ i j, WeakPartial univ (fun x => R.j x j) (R.currentDerivative i j) i) ∧
      (∀ᵐ x, (∑ i, R.currentDerivative i i x) = 0) := by
  obtain ⟨R⟩ := elliptic A V E hA hV W
  exact ⟨R, R.current_weak L hA, R.current_divergence_zero⟩

end MagHK.OneParticleWeak
