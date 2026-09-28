import NavierStokesAB.SmallData.Lattice

/-!
# Fourier series on `ℝ³/ℤ³` with rapidly decaying coefficients

For coefficients `c : Λ → E` in a complex Banach space with `Σ |k|^m ‖c k‖ < ∞` for every `m`
(`RapidDecay c`), the series `four c x = Σ_k e_k(x) • c k`, `e_k(x) = exp(2πi⟪k, x⟫)`, is:

* differentiable, with derivative the series of the derivative coefficients `dcoef c`
  (`hasFDerivAt_four`); in particular `fderiv (four c) x h = four (k ↦ 2πi⟪k, h⟫ c k) x`;
* `C^∞` (`contDiff_four`), by induction since `dcoef c` again decays rapidly;
* `Δ (four c) = four (k ↦ -λ_k c k)` (`laplacian_four`);
* `1`-periodic in every coordinate (`four_add_single`).
-/

open Real Complex
open scoped InnerProductSpace ContDiff Laplacian

set_option synthInstance.maxHeartbeats 200000

namespace NavierStokesAB.SmallData

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `h ↦ 2πi⟪k, h⟫`. -/
noncomputable def Lk (k : Λ) : ℝ³ →L[ℝ] ℂ :=
  (2 * π * I) • (Complex.ofRealCLM.comp (innerSL ℝ (kR k)))

theorem Lk_apply (k : Λ) (h : ℝ³) : Lk k h = 2 * π * I * (⟪kR k, h⟫_ℝ : ℂ) := by
  simp [Lk]

theorem norm_Lk_apply_le (k : Λ) (h : ℝ³) : ‖Lk k h‖ ≤ 2 * π * kn k * ‖h‖ := by
  rw [Lk_apply, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg pi_pos.le, Real.norm_eq_abs]
  have := abs_real_inner_le_norm (kR k) h
  unfold kn
  nlinarith [pi_pos]

theorem norm_Lk_le (k : Λ) : ‖Lk k‖ ≤ 2 * π * kn k :=
  ContinuousLinearMap.opNorm_le_bound _ (by have := kn_nonneg k; positivity) (norm_Lk_apply_le k)

/-- The Fourier mode `e_k(x) = exp(2πi⟪k, x⟫)`. -/
noncomputable def emode (k : Λ) (x : ℝ³) : ℂ := Complex.exp (Lk k x)

theorem norm_emode (k : Λ) (x : ℝ³) : ‖emode k x‖ = 1 := by
  rw [emode, Complex.norm_exp, Lk_apply]
  simp

theorem hasFDerivAt_emode (k : Λ) (x : ℝ³) :
    HasFDerivAt (emode k) (emode k x • Lk k) x :=
  (Lk k).hasFDerivAt.cexp

theorem emode_add_single (k : Λ) (x : ℝ³) (i : Fin 3) :
    emode k (x + EuclideanSpace.single i 1) = emode k x := by
  rw [emode, emode, map_add, Complex.exp_add, Lk_apply (h := EuclideanSpace.single i 1)]
  have : Complex.exp (2 * π * I * ((⟪kR k, EuclideanSpace.single i (1 : ℝ)⟫_ℝ : ℝ) : ℂ)) = 1 := by
    rw [EuclideanSpace.inner_single_right]
    simp only [kR_apply, conj_trivial, one_mul, Complex.ofReal_intCast]
    rw [show 2 * π * I * ((k i : ℤ) : ℂ) = (k i : ℤ) * (2 * π * I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I (k i)
  rw [this, mul_one]

/-! ### Rapid decay -/

/-- Coefficients decaying faster than any power of `|k|`. -/
def RapidDecay {E : Type*} [NormedAddCommGroup E] (c : Λ → E) : Prop :=
  ∀ m : ℕ, Summable fun k => kn k ^ m * ‖c k‖

section Four

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem RapidDecay.summable_norm {c : Λ → E} (hc : RapidDecay c) : Summable fun k => ‖c k‖ := by
  simpa using hc 0

/-- The Fourier series with coefficients `c`. -/
noncomputable def four (c : Λ → E) (x : ℝ³) : E := ∑' k, emode k x • c k

theorem summable_four {c : Λ → E} (hc : RapidDecay c) (x : ℝ³) :
    Summable fun k => emode k x • c k :=
  Summable.of_norm_bounded hc.summable_norm fun k => by rw [norm_smul, norm_emode, one_mul]

/-- The coefficients of the derivative. -/
noncomputable def dcoef (c : Λ → E) (k : Λ) : ℝ³ →L[ℝ] E := (Lk k).smulRight (c k)

theorem dcoef_apply (c : Λ → E) (k : Λ) (h : ℝ³) : dcoef c k h = Lk k h • c k := rfl

theorem norm_dcoef_le (c : Λ → E) (k : Λ) : ‖dcoef c k‖ ≤ 2 * π * kn k * ‖c k‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by have := kn_nonneg k; positivity) fun h => by
    rw [dcoef_apply, norm_smul]
    calc ‖Lk k h‖ * ‖c k‖ ≤ 2 * π * kn k * ‖h‖ * ‖c k‖ := by
          gcongr; exact norm_Lk_apply_le k h
      _ = 2 * π * kn k * ‖c k‖ * ‖h‖ := by ring

theorem RapidDecay.deriv {c : Λ → E} (hc : RapidDecay c) : RapidDecay (dcoef c) := fun m =>
  ((hc (m + 1)).mul_left (2 * π)).of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (kn_nonneg k) m) (norm_nonneg _)) fun k => by
      calc kn k ^ m * ‖dcoef c k‖ ≤ kn k ^ m * (2 * π * kn k * ‖c k‖) :=
            mul_le_mul_of_nonneg_left (norm_dcoef_le c k) (pow_nonneg (kn_nonneg k) m)
        _ = 2 * π * (kn k ^ (m + 1) * ‖c k‖) := by ring

theorem hasFDerivAt_four {c : Λ → E} (hc : RapidDecay c) (x : ℝ³) :
    HasFDerivAt (four c) (four (dcoef c) x) x := by
  have hd : ∀ k y, HasFDerivAt (fun y => emode k y • c k) (emode k y • dcoef c k) y := by
    intro k y
    refine ((hasFDerivAt_emode k y).smul_const (c k)).congr_fderiv ?_
    ext h
    simp [dcoef_apply, smul_smul]
  have hu : Summable fun k => 2 * π * kn k * ‖c k‖ :=
    ((hc 1).mul_left (2 * π)).congr fun k => by ring
  exact hasFDerivAt_tsum hu hd
    (fun k y => by
      rw [norm_smul, norm_emode, one_mul]
      exact norm_dcoef_le c k)
    (summable_four hc 0) x

theorem fderiv_four {c : Λ → E} (hc : RapidDecay c) : fderiv ℝ (four c) = four (dcoef c) :=
  funext fun x => (hasFDerivAt_four hc x).fderiv

theorem four_apply_clm {c : Λ → ℝ³ →L[ℝ] E} (hc : RapidDecay c) (x h : ℝ³) :
    four c x h = four (fun k => c k h) x := by
  have h1 := (ContinuousLinearMap.apply ℝ E h).map_tsum (summable_four hc x)
  simp only [ContinuousLinearMap.apply_apply] at h1
  unfold four
  rw [h1]
  simp

theorem fderiv_four_apply {c : Λ → E} (hc : RapidDecay c) (x h : ℝ³) :
    fderiv ℝ (four c) x h = four (fun k => Lk k h • c k) x := by
  rw [fderiv_four hc, four_apply_clm hc.deriv]
  rfl

theorem continuous_four {c : Λ → E} (hc : RapidDecay c) : Continuous (four c) :=
  continuous_tsum (fun k => (Complex.continuous_exp.comp (Lk k).continuous).smul
    continuous_const) hc.summable_norm fun k x => by rw [norm_smul, norm_emode, one_mul]

theorem contDiff_four_nat (n : ℕ) :
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {c : Λ → E},
      RapidDecay c → ContDiff ℝ n (four c) := by
  induction n with
  | zero => intro E _ _ _ c hc; exact contDiff_zero.2 (continuous_four hc)
  | succ n ih =>
    intro E _ _ _ c hc
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_four hc x).differentiableAt, by simp, ?_⟩
    rw [fderiv_four hc]
    exact ih hc.deriv

theorem contDiff_four {c : Λ → E} (hc : RapidDecay c) : ContDiff ℝ ∞ (four c) :=
  contDiff_infty.2 fun n => contDiff_four_nat n hc

theorem four_add_single (c : Λ → E) (x : ℝ³) (i : Fin 3) :
    four c (x + EuclideanSpace.single i 1) = four c x := by
  simp only [four, emode_add_single]

/-! ### The Laplacian -/

theorem Lk_basisFun (k : Λ) (i : Fin 3) :
    Lk k (EuclideanSpace.basisFun (Fin 3) ℝ i) = 2 * π * I * (k i : ℂ) := by
  rw [Lk_apply, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]
  simp

theorem sum_Lk_sq (k : Λ) :
    ∑ i, Lk k (EuclideanSpace.basisFun (Fin 3) ℝ i) * Lk k (EuclideanSpace.basisFun (Fin 3) ℝ i) =
      -((4 * π ^ 2 * kn k ^ 2 : ℝ) : ℂ) := by
  simp only [Lk_basisFun]
  have hk : kn k ^ 2 = ∑ i, ((k i : ℝ)) ^ 2 := by
    unfold kn
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hk, Fin.sum_univ_three, Fin.sum_univ_three]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem laplacian_four {c : Λ → E} (hc : RapidDecay c) (x : ℝ³) :
    Δ (four c) x = four (fun k => (-((4 * π ^ 2 * kn k ^ 2 : ℝ) : ℂ)) • c k) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [fderiv_four hc, fderiv_four hc.deriv]
  set b := EuclideanSpace.basisFun (Fin 3) ℝ
  have h2 : ∀ i, four (dcoef (dcoef c)) x (b i) (b i) =
      four (fun k => (Lk k (b i) * Lk k (b i)) • c k) x := by
    intro i
    rw [four_apply_clm hc.deriv.deriv, four_apply_clm (c := fun k => dcoef (dcoef c) k (b i))]
    · congr 1
      funext k
      simp [dcoef_apply, smul_smul]
    · -- rapid decay of the partially applied coefficients
      intro m
      refine (hc.deriv.deriv m).of_nonneg_of_le
        (fun k => mul_nonneg (pow_nonneg (kn_nonneg k) m) (norm_nonneg _)) fun k => ?_
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (kn_nonneg k) m)
      calc ‖dcoef (dcoef c) k (b i)‖ ≤ ‖dcoef (dcoef c) k‖ * ‖b i‖ := (dcoef (dcoef c) k).le_opNorm _
        _ = ‖dcoef (dcoef c) k‖ := by simp [b, EuclideanSpace.basisFun_apply]
  simp only [h2]
  unfold four
  have hs : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun k => emode k x • (Lk k (b i) * Lk k (b i)) • c k := by
    intro i _
    refine Summable.of_norm_bounded (((hc 2).mul_left (4 * π ^ 2))) fun k => ?_
    rw [norm_smul, norm_emode, one_mul, norm_smul, norm_mul]
    have h1 := norm_Lk_apply_le k (b i)
    have hb : ‖b i‖ = 1 := by simp [b, EuclideanSpace.basisFun_apply]
    rw [hb, mul_one] at h1
    have hk0 : 0 ≤ 2 * π * kn k := mul_nonneg (by positivity) (kn_nonneg k)
    calc ‖Lk k (b i)‖ * ‖Lk k (b i)‖ * ‖c k‖ ≤ (2 * π * kn k) * (2 * π * kn k) * ‖c k‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h1 (norm_nonneg _) hk0) (norm_nonneg _)
      _ = 4 * π ^ 2 * (kn k ^ 2 * ‖c k‖) := by ring
  rw [← Summable.tsum_finsetSum hs]
  congr 1
  funext k
  rw [← Finset.smul_sum, ← Finset.sum_smul, sum_Lk_sq]

end Four

end NavierStokesAB.SmallData
