import NavierStokesAB.SmallData.Duhamel

/-!
# The Navier–Stokes symbols in Fourier variables

Velocity Fourier coefficients live in `V = ℂ³`. For a frequency `k`:
* `kC k` is `k` as a vector of `ℂ³`; `⟪kC k, z⟫ = Σ kᵢ zᵢ` since `k` is real;
* `leray k` is the orthogonal projection onto `kᗮ` (the Leray projector), of norm `≤ 1`;
* `nl k x y = -2πi · P_k(⟪k, x⟫ y)` is the Fourier symbol of `-P ∇·(u ⊗ w)`, of norm `≤ 2π|k|`.
-/

open Real Complex
open scoped NNReal BoundedContinuousFunction InnerProductSpace

namespace NavierStokesAB.SmallData

/-- Fourier coefficients of velocity fields. -/
abbrev V := EuclideanSpace ℂ (Fin 3)

/-- A frequency as a vector of `ℂ³`. -/
noncomputable def kC (k : Λ) : V := WithLp.toLp 2 fun i => (k i : ℂ)

@[simp] theorem kC_apply (k : Λ) (i : Fin 3) : kC k i = k i := rfl

theorem norm_kC (k : Λ) : ‖kC k‖ = kn k := by
  unfold kn
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.norm_intCast, Real.norm_eq_abs]

theorem kC_neg (k : Λ) : kC (-k) = -kC k := by
  ext i; simp

@[simp] theorem kC_zero : kC 0 = 0 := by
  ext i; simp

theorem inner_kC (k : Λ) (z : V) : ⟪kC k, z⟫_ℂ = ∑ i, (k i : ℂ) * z i := by
  simp [PiLp.inner_apply, mul_comm]

/-! ### The Leray projector -/

/-- Orthogonal projection onto `kᗮ`. -/
noncomputable def leray (k : Λ) : V →L[ℂ] V := (ℂ ∙ kC k)ᗮ.starProjection

theorem norm_leray_le (k : Λ) : ‖leray k‖ ≤ 1 := Submodule.starProjection_norm_le _

theorem leray_apply (k : Λ) (z : V) :
    leray k z = z - (⟪kC k, z⟫_ℂ / ((‖kC k‖ ^ 2 : ℝ) : ℂ)) • kC k := by
  rw [leray, Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton]
  rfl

theorem inner_kC_leray (k : Λ) (z : V) : ⟪kC k, leray k z⟫_ℂ = 0 := by
  have h : leray k z ∈ (ℂ ∙ kC k)ᗮ := Submodule.starProjection_apply_mem _ z
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at h
  exact h

theorem leray_neg (k : Λ) : leray (-k) = leray k := by
  ext1 z
  rw [leray_apply, leray_apply, kC_neg, inner_neg_left, norm_neg, neg_div, neg_smul_neg]

theorem norm_leray_apply_le (k : Λ) (z : V) : ‖leray k z‖ ≤ ‖z‖ :=
  calc ‖leray k z‖ ≤ ‖leray k‖ * ‖z‖ := (leray k).le_opNorm z
    _ ≤ 1 * ‖z‖ := by gcongr; exact norm_leray_le k
    _ = ‖z‖ := one_mul _

/-! ### The nonlinear symbol -/

/-- `x ↦ (y ↦ ⟪k, x⟫ y)`. -/
noncomputable def dotSmul (k : Λ) : V →L[ℂ] V →L[ℂ] V :=
  (innerSL ℂ (kC k)).smulRight (ContinuousLinearMap.id ℂ V)

theorem dotSmul_apply (k : Λ) (x y : V) : dotSmul k x y = ⟪kC k, x⟫_ℂ • y := by
  simp [dotSmul]

/-- The Fourier symbol of `-P ∇·(u ⊗ w)` at frequency `k`: `(x, y) ↦ -2πi P_k(⟪k, x⟫ y)`. -/
noncomputable def nl (k : Λ) : V →L[ℂ] V →L[ℂ] V :=
  (-(2 * π * I) : ℂ) • (ContinuousLinearMap.compL ℂ V V V (leray k)).comp (dotSmul k)

theorem nl_apply (k : Λ) (x y : V) :
    nl k x y = (-(2 * π * I) : ℂ) • leray k (⟪kC k, x⟫_ℂ • y) := by
  simp [nl, dotSmul_apply]

theorem norm_nl_apply_le (k : Λ) (x y : V) : ‖nl k x y‖ ≤ 2 * π * kn k * ‖x‖ * ‖y‖ := by
  rw [nl_apply, norm_smul]
  have h1 : ‖(-(2 * π * I) : ℂ)‖ = 2 * π := by
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  have h2 : ‖leray k (⟪kC k, x⟫_ℂ • y)‖ ≤ kn k * ‖x‖ * ‖y‖ := by
    calc ‖leray k (⟪kC k, x⟫_ℂ • y)‖ ≤ ‖⟪kC k, x⟫_ℂ • y‖ := norm_leray_apply_le k _
      _ = ‖⟪kC k, x⟫_ℂ‖ * ‖y‖ := norm_smul _ _
      _ ≤ ‖kC k‖ * ‖x‖ * ‖y‖ := by gcongr; exact norm_inner_le_norm _ _
      _ = kn k * ‖x‖ * ‖y‖ := by rw [norm_kC]
  rw [h1]
  calc 2 * π * ‖leray k (⟪kC k, x⟫_ℂ • y)‖ ≤ 2 * π * (kn k * ‖x‖ * ‖y‖) := by
        gcongr
    _ = 2 * π * kn k * ‖x‖ * ‖y‖ := by ring

theorem norm_nl_le (k : Λ) : ‖nl k‖ ≤ 2 * π * kn k :=
  ContinuousLinearMap.opNorm_le_bound₂ _ (by have := kn_nonneg k; positivity)
    (norm_nl_apply_le k)

theorem inner_kC_nl (k : Λ) (x y : V) : ⟪kC k, nl k x y⟫_ℂ = 0 := by
  rw [nl_apply, inner_smul_right, inner_kC_leray, mul_zero]

@[simp] theorem nl_zero_freq : nl 0 = 0 := by
  ext x y i
  simp [nl_apply, kC_zero]

/-! ### Frequency-dependent constants -/

/-- The Laplacian symbol `λ_k = 4π²|k|²`. -/
noncomputable def lam (k : Λ) : ℝ := 4 * π ^ 2 * kn k ^ 2

theorem lam_nonneg (k : Λ) : 0 ≤ lam k := by unfold lam; positivity

theorem lam_pos {k : Λ} (hk : k ≠ 0) : 0 < lam k := by
  have := one_le_kn hk
  unfold lam; positivity

@[simp] theorem lam_neg (k : Λ) : lam (-k) = lam k := by simp [lam]

end NavierStokesAB.SmallData
