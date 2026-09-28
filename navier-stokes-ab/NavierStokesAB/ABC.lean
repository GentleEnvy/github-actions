import NavierStokesAB.Beltrami

/-!
# Arnold–Beltrami–Childress flows: explicit global solutions for (B)

For `m : ℤ`, `k = 2πm` and amplitudes `A B C : ℝ`, the ABC field
```
  U(x) = (A sin(k x₂) + C cos(k x₁),
          B sin(k x₀) + A cos(k x₂),
          C sin(k x₁) + B cos(k x₀))
```
is smooth, `1`-periodic, divergence free, satisfies `Δ U = -k² U` and `curl U = k U`.
By `NavierStokesAB.IsBeltrami.periodicSolution` it evolves as `e^{-ν k² t} U` for all time.
So Clay (B) holds for every datum in this four-parameter family, for every viscosity.

We build `U` from plane waves `x ↦ φ ⟪d, x⟫ • e`.
-/

open NavierStokes.Comparator InnerProductSpace Laplacian Set Real
open scoped ContDiff RealInnerProductSpace

namespace NavierStokesAB

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ### Plane waves -/

section PlaneWave

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The plane wave `x ↦ φ ⟪d, x⟫ • e`. -/
noncomputable def planeWave (φ : ℝ → ℝ) (d : E) (e : F) (x : E) : F := φ ⟪d, x⟫ • e

variable {φ φ' φ'' : ℝ → ℝ}

theorem hasFDerivAt_planeWave (hφ : ∀ s, HasDerivAt φ (φ' s) s) (d : E) (e : F) (x : E) :
    HasFDerivAt (planeWave φ d e) (φ' ⟪d, x⟫ • (innerSL ℝ d).smulRight e) x := by
  have h := ((hφ ⟪d, x⟫).comp_hasFDerivAt x (innerSL ℝ d).hasFDerivAt).smul_const e
  show HasFDerivAt (fun y => (φ ∘ fun y => innerSL ℝ d y) y • e) _ x
  convert h using 1
  ext w
  simp [smul_smul]

theorem fderiv_planeWave (hφ : ∀ s, HasDerivAt φ (φ' s) s) (d : E) (e : F) :
    fderiv ℝ (planeWave φ d e) = planeWave φ' d ((innerSL ℝ d).smulRight e) := by
  funext x
  exact (hasFDerivAt_planeWave hφ d e x).fderiv

theorem fderiv_planeWave_apply (hφ : ∀ s, HasDerivAt φ (φ' s) s) (d : E) (e : F) (x w : E) :
    fderiv ℝ (planeWave φ d e) x w = (φ' ⟪d, x⟫ * ⟪d, w⟫) • e := by
  rw [(hasFDerivAt_planeWave hφ d e x).fderiv]
  simp [smul_smul]

theorem contDiff_planeWave (hφ : ContDiff ℝ ∞ φ) (d : E) (e : F) :
    ContDiff ℝ ∞ (planeWave φ d e) :=
  (hφ.comp (contDiff_const.inner contDiff_id)).smul contDiff_const

theorem laplacian_planeWave [FiniteDimensional ℝ E] (hφ : ∀ s, HasDerivAt φ (φ' s) s)
    (hφ' : ∀ s, HasDerivAt φ' (φ'' s) s) (d : E) (e : F) (x : E) :
    Δ (planeWave φ d e) x = (‖d‖ ^ 2 * φ'' ⟪d, x⟫) • e := by
  set b := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_planeWave hφ, fderiv_planeWave hφ']
  simp only [planeWave, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_smul, ← Finset.sum_smul]
  congr 1
  have h := b.sum_inner_mul_inner d d
  simp only [real_inner_comm (b _) d] at h
  rw [← real_inner_self_eq_norm_sq, ← h, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end PlaneWave

/-! ### The ABC field -/

/-- Shorthand for the coordinate vectors of `ℝ³` scaled by `a`. -/
local notation "𝐞" i:max a:max => EuclideanSpace.single (𝕜 := ℝ) (i : Fin 3) a

/-- The wave number `2πm`. -/
local notation "𝐤" m:max => (2 * π * (m : ℝ))

/-- The ABC field with wave number `2πm` and amplitudes `A, B, C`. -/
noncomputable def abc (m : ℤ) (A B C : ℝ) : ℝ³ → ℝ³ :=
  planeWave sin (𝐞 2 (𝐤 m)) (𝐞 0 A) + planeWave cos (𝐞 1 (𝐤 m)) (𝐞 0 C) +
  planeWave sin (𝐞 0 (𝐤 m)) (𝐞 1 B) + planeWave cos (𝐞 2 (𝐤 m)) (𝐞 1 A) +
  planeWave sin (𝐞 1 (𝐤 m)) (𝐞 2 C) + planeWave cos (𝐞 0 (𝐤 m)) (𝐞 2 B)

variable (m : ℤ) (A B C : ℝ)

theorem abc_apply (x : ℝ³) :
    abc m A B C x = !₂[A * sin (2 * π * m * x 2) + C * cos (2 * π * m * x 1),
      B * sin (2 * π * m * x 0) + A * cos (2 * π * m * x 2),
      C * sin (2 * π * m * x 1) + B * cos (2 * π * m * x 0)] := by
  ext i
  fin_cases i <;>
    simp [abc, planeWave, EuclideanSpace.inner_single_left] <;> ring

theorem contDiff_abc : ContDiff ℝ ∞ (abc m A B C) := by
  have hs := contDiff_sin (n := ∞)
  have hc := contDiff_cos (n := ∞)
  unfold abc
  exact (((((contDiff_planeWave hs _ _).add (contDiff_planeWave hc _ _)).add
    (contDiff_planeWave hs _ _)).add (contDiff_planeWave hc _ _)).add
    (contDiff_planeWave hs _ _)).add (contDiff_planeWave hc _ _)

theorem hasFDerivAt_abc (x : ℝ³) :
    HasFDerivAt (abc m A B C)
      (cos ⟪𝐞 2 (𝐤 m), x⟫ • (innerSL ℝ (𝐞 2 (𝐤 m))).smulRight (𝐞 0 A) +
       -sin ⟪𝐞 1 (𝐤 m), x⟫ • (innerSL ℝ (𝐞 1 (𝐤 m))).smulRight (𝐞 0 C) +
       cos ⟪𝐞 0 (𝐤 m), x⟫ • (innerSL ℝ (𝐞 0 (𝐤 m))).smulRight (𝐞 1 B) +
       -sin ⟪𝐞 2 (𝐤 m), x⟫ • (innerSL ℝ (𝐞 2 (𝐤 m))).smulRight (𝐞 1 A) +
       cos ⟪𝐞 1 (𝐤 m), x⟫ • (innerSL ℝ (𝐞 1 (𝐤 m))).smulRight (𝐞 2 C) +
       -sin ⟪𝐞 0 (𝐤 m), x⟫ • (innerSL ℝ (𝐞 0 (𝐤 m))).smulRight (𝐞 2 B)) x := by
  have hs : ∀ s, HasDerivAt sin (cos s) s := hasDerivAt_sin
  have hc : ∀ s, HasDerivAt cos (-sin s) s := hasDerivAt_cos
  unfold abc
  exact (((((hasFDerivAt_planeWave hs _ _ x).add (hasFDerivAt_planeWave hc _ _ x)).add
    (hasFDerivAt_planeWave hs _ _ x)).add (hasFDerivAt_planeWave hc _ _ x)).add
    (hasFDerivAt_planeWave hs _ _ x)).add (hasFDerivAt_planeWave hc _ _ x)

theorem fderiv_abc_apply (x w : ℝ³) :
    fderiv ℝ (abc m A B C) x w = !₂[
      2 * π * m * (A * cos (2 * π * m * x 2) * w 2 - C * sin (2 * π * m * x 1) * w 1),
      2 * π * m * (B * cos (2 * π * m * x 0) * w 0 - A * sin (2 * π * m * x 2) * w 2),
      2 * π * m * (C * cos (2 * π * m * x 1) * w 1 - B * sin (2 * π * m * x 0) * w 0)] := by
  rw [(hasFDerivAt_abc m A B C x).fderiv]
  ext i
  fin_cases i <;>
    simp [EuclideanSpace.inner_single_left] <;> ring

theorem divergence_abc (x : ℝ³) : divergence (abc m A B C) x = 0 := by
  rw [divergence, LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [Fin.sum_univ_three, fderiv_abc_apply, EuclideanSpace.inner_single_left]

theorem laplacian_abc (x : ℝ³) : Δ (abc m A B C) x = -(2 * π * m) ^ 2 • abc m A B C x := by
  have hs : ∀ s, HasDerivAt sin (cos s) s := hasDerivAt_sin
  have hc : ∀ s, HasDerivAt cos (-sin s) s := hasDerivAt_cos
  have hc' : ∀ s, HasDerivAt (fun s => -sin s) (-cos s) s := fun s => (hasDerivAt_sin s).neg
  have two : (2 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have la : ∀ {f₁ f₂ : ℝ³ → ℝ³}, ContDiff ℝ ∞ f₁ → ContDiff ℝ ∞ f₂ →
      Δ (f₁ + f₂) x = Δ f₁ x + Δ f₂ x :=
    fun h₁ h₂ => ContDiffAt.laplacian_add (h₁.contDiffAt.of_le two) (h₂.contDiffAt.of_le two)
  have ca : ∀ {f₁ f₂ : ℝ³ → ℝ³}, ContDiff ℝ ∞ f₁ → ContDiff ℝ ∞ f₂ → ContDiff ℝ ∞ (f₁ + f₂) :=
    fun h₁ h₂ => h₁.add h₂
  unfold abc
  rw [la _ _, la _ _, la _ _, la _ _, la _ _,
    laplacian_planeWave hs hc, laplacian_planeWave hc hc', laplacian_planeWave hs hc,
    laplacian_planeWave hc hc', laplacian_planeWave hs hc, laplacian_planeWave hc hc']
  · ext i
    fin_cases i <;>
      simp [planeWave, EuclideanSpace.inner_single_left, PiLp.norm_single] <;> ring
  all_goals
    repeat' apply ca
    all_goals first
      | exact contDiff_planeWave contDiff_sin _ _
      | exact contDiff_planeWave contDiff_cos _ _

theorem lamb_abc (x w : ℝ³) :
    ⟪fderiv ℝ (abc m A B C) x (abc m A B C x), w⟫ =
      ⟪abc m A B C x, fderiv ℝ (abc m A B C) x w⟫ := by
  rw [fderiv_abc_apply, fderiv_abc_apply, abc_apply]
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem isOnePeriodic_abc : IsOnePeriodic (abc m A B C) := by
  intro x i
  have hs : ∀ y : ℝ, sin (y + 2 * π * m) = sin y := fun y => by
    rw [show 2 * π * (m : ℝ) = m * (2 * π) by ring, sin_add_int_mul_two_pi]
  have hc : ∀ y : ℝ, cos (y + 2 * π * m) = cos y := fun y => by
    rw [show 2 * π * (m : ℝ) = m * (2 * π) by ring, cos_add_int_mul_two_pi]
  rw [abc_apply, abc_apply]
  fin_cases i <;>
    simp [mul_add, hs, hc]

theorem isBeltrami_abc : IsBeltrami ((2 * π * m) ^ 2) (abc m A B C) where
  smooth := contDiff_abc m A B C
  div_free := divergence_abc m A B C
  laplacian_eq := laplacian_abc m A B C
  lamb := lamb_abc m A B C

/-- Every ABC datum is admissible for Clay (B). -/
theorem initialVelocityConditionPeriodic_abc :
    InitialVelocityConditionPeriodic (abc m A B C) :=
  (isBeltrami_abc m A B C).initialVelocityConditionPeriodic (isOnePeriodic_abc m A B C)

/-- **Clay (B) for ABC data.** For every viscosity (in particular every `nu > 0`), the ABC
datum has the global smooth periodic solution `e^{-ν k² t} U`, with `k = 2πm`. -/
theorem existencePeriodic_abc (nu : ℝ) :
    ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu (abc m A B C) (f := 0) v p :=
  ⟨_, _, (isBeltrami_abc m A B C).periodicSolution nu (isOnePeriodic_abc m A B C)⟩

end NavierStokesAB
