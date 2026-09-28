import NavierStokesAB.SmallData.Setup
import NavierStokes.ComparatorDefinitions

/-!
# Clay (B) for small analytic data

We check, one field at a time, that the velocity and pressure attached to `Small ν σ₀ a` form a
solution in the class `NavierStokesExistenceAndSmoothnessPeriodic` of the Clay/Formal Conjectures
formalization, with initial datum `datum σ₀ a` and zero force; and that this datum is admissible
(`InitialVelocityConditionPeriodic`).
-/

open Real Complex Set Filter Topology MeasureTheory
open scoped NNReal BoundedContinuousFunction InnerProductSpace ComplexConjugate ContDiff Laplacian

open NavierStokes.Comparator

set_option synthInstance.maxHeartbeats 200000

namespace NavierStokesAB.SmallData

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ### Calculus for real parts of Fourier series -/

section Calculus

theorem fderiv_re3_four {c : Λ → V} (hc : RapidDecay c) (x u : ℝ³) :
    fderiv ℝ (fun y => re3 (four c y)) x u = re3 (four (fun k => Lk k u • c k) x) := by
  have hd : HasFDerivAt (fun y => re3 (four c y)) (re3.comp (four (dcoef c) x)) x :=
    re3.hasFDerivAt.comp x (hasFDerivAt_four hc x)
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, four_apply_clm hc.deriv]
  rfl

theorem laplacian_re3_four {c : Λ → V} (hc : RapidDecay c) (x : ℝ³) :
    Δ (fun y => re3 (four c y)) x =
      re3 (four (fun k => (-((4 * π ^ 2 * kn k ^ 2 : ℝ) : ℂ)) • c k) x) := by
  have h2 : ContDiffAt ℝ 2 (four c) x := ((contDiff_four hc).of_le (by simp)).contDiffAt
  rw [show (fun y => re3 (four c y)) = re3 ∘ four c from rfl,
    ContDiffAt.laplacian_CLM_comp_left h2, Function.comp_apply, laplacian_four hc]

theorem four_coord {c : Λ → V} (hc : RapidDecay c) (x : ℝ³) (i : Fin 3) :
    four c x i = four (fun k => c k i) x := by
  have := four_map (EuclideanSpace.proj i : V →L[ℂ] ℂ) hc x
  simpa using this

theorem four_finset_sum {ι : Type*} (s : Finset ι) {c : ι → Λ → ℂ}
    (hc : ∀ i ∈ s, RapidDecay (c i)) (x : ℝ³) :
    ∑ i ∈ s, four (c i) x = four (fun k => ∑ i ∈ s, c i k) x := by
  unfold four
  rw [← Summable.tsum_finsetSum fun i hi => summable_four (hc i hi) x]
  simp [Finset.mul_sum]

theorem rapidDecay_Lk_smul {c : Λ → V} (hc : RapidDecay c) (u : ℝ³) :
    RapidDecay fun k => Lk k u • c k :=
  RapidDecay.of_norm_le hc.deriv (C := ‖u‖) fun k => by
    rw [show Lk k u • c k = dcoef c k u from rfl, mul_comm]
    exact (dcoef c k).le_opNorm u

theorem divergence_re3_four {c : Λ → V} (hc : RapidDecay c) (hdiv : ∀ k, ⟪kC k, c k⟫_ℂ = 0)
    (x : ℝ³) : divergence (fun y => re3 (four c y)) x = 0 := by
  set b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hdc : ∀ i : Fin 3, RapidDecay fun k => Lk k (b i) * c k i := fun i =>
    RapidDecay.of_norm_le hc.deriv fun k => by
      rw [show Lk k (b i) * c k i = dcoef c k (b i) i by simp [dcoef_apply]]
      calc ‖dcoef c k (b i) i‖ ≤ ‖dcoef c k (b i)‖ := PiLp.norm_apply_le _ i
        _ ≤ ‖dcoef c k‖ * ‖b i‖ := (dcoef c k).le_opNorm _
        _ = 1 * ‖dcoef c k‖ := by simp [b, EuclideanSpace.basisFun_apply]
  rw [divergence, LinearMap.trace_eq_sum_inner _ b]
  have hterm : ∀ i : Fin 3, ⟪b i, (fderiv ℝ (fun y => re3 (four c y)) x) (b i)⟫_ℝ =
      (four (fun k => Lk k (b i) * c k i) x).re := by
    intro i
    rw [fderiv_re3_four hc, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
      re3_apply, four_coord (rapidDecay_Lk_smul hc _)]
    simp
  simp only [ContinuousLinearMap.coe_coe, hterm]
  rw [← Complex.re_sum, four_finset_sum _ fun i _ => hdc i]
  have hz : ∀ k, ∑ i, Lk k (b i) * c k i = 0 := by
    intro k
    have := hdiv k
    rw [inner_kC] at this
    calc ∑ i, Lk k (b i) * c k i = ∑ i, (2 * π * I) * ((k i : ℂ) * c k i) :=
          Finset.sum_congr rfl fun i _ => by rw [Lk_basisFun]; ring
      _ = (2 * π * I) * ∑ i, (k i : ℂ) * c k i := by rw [Finset.mul_sum]
      _ = 0 := by rw [this, mul_zero]
  simp [hz]

theorem inner_gradient_eq {f : ℝ³ → ℝ} (x u : ℝ³) : ⟪gradient f x, u⟫_ℝ = fderiv ℝ f x u := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

theorem fderiv_re_four {q : Λ → ℂ} (hq : RapidDecay q) (x u : ℝ³) :
    fderiv ℝ (fun y => (four q y).re) x u = (four (fun n => Lk n u * q n) x).re := by
  have hd : HasFDerivAt (fun y => (four q y).re) (Complex.reCLM.comp (four (dcoef q) x)) x :=
    Complex.reCLM.hasFDerivAt.comp x (hasFDerivAt_four hq x)
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, four_apply_clm hq.deriv]
  simp [dcoef_apply]

theorem RapidDecay.of_norm_le_pow {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {c : Λ → E} {c' : Λ → F} (hc : RapidDecay c) (C : ℝ) (p : ℕ)
    (h : ∀ k, ‖c' k‖ ≤ C * (kn k ^ p * ‖c k‖)) : RapidDecay c' := fun m =>
  ((hc (m + p)).mul_left C).of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (kn_nonneg k) m) (norm_nonneg _)) fun k => by
      calc kn k ^ m * ‖c' k‖ ≤ kn k ^ m * (C * (kn k ^ p * ‖c k‖)) :=
            mul_le_mul_of_nonneg_left (h k) (pow_nonneg (kn_nonneg k) m)
        _ = C * (kn k ^ (m + p) * ‖c k‖) := by ring

theorem RapidDecay.inner {c : Λ → V} (hc : RapidDecay c) (z : V) :
    RapidDecay fun k => ⟪z, c k⟫_ℂ :=
  hc.of_norm_le (C := ‖z‖) fun _ => norm_inner_le_norm _ _

theorem RapidDecay.lap {c : Λ → V} (hc : RapidDecay c) :
    RapidDecay fun k => (-((4 * π ^ 2 * kn k ^ 2 : ℝ) : ℂ)) • c k :=
  hc.of_norm_le_pow (4 * π ^ 2) 2 fun k => le_of_eq (by
    rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    ring)

theorem inner_four {c : Λ → V} (hc : RapidDecay c) (z : V) (x : ℝ³) :
    ⟪z, four c x⟫_ℂ = four (fun k => ⟪z, c k⟫_ℂ) x := by
  have := four_map (innerSL ℂ z) hc x
  simpa only [innerSL_apply_apply] using this

theorem four_lin {c₁ c₂ c₃ : Λ → ℂ} (h₁ : RapidDecay c₁) (h₂ : RapidDecay c₂)
    (h₃ : RapidDecay c₃) (r : ℂ) (x : ℝ³) :
    four (fun k => r * c₁ k - c₂ k - c₃ k) x = r * four c₁ x - four c₂ x - four c₃ x := by
  have H := (((summable_four h₁ x).hasSum.mul_left r).sub (summable_four h₂ x).hasSum).sub
    (summable_four h₃ x).hasSum
  unfold four
  rw [← H.tsum_eq]
  congr 1
  funext k
  simp only [smul_eq_mul]
  ring

theorem inner_ofReal3_kC (e : ℝ³) (k : Λ) : ⟪ofReal3 e, kC k⟫_ℂ = ((⟪kR k, e⟫_ℝ : ℝ) : ℂ) := by
  rw [← inner_conj_symm, inner_kC_ofReal3, Complex.conj_ofReal]

end Calculus

namespace Small

variable {ν σ₀ : ℝ} {a : D} (h : Small ν σ₀ a)
include h

/-! ### Smoothness -/

theorem contDiffOn_w : ContDiffOn ℝ ∞ h.w (Ici 0) :=
  contDiffOn_curve h.sol_fix h.half_pos.le h.half_lt

theorem contDiffOn_w_snd :
    ContDiffOn ℝ ∞ (fun q : ℝ³ × ℝ => h.w q.2) (univ ×ˢ Ici 0) :=
  h.contDiffOn_w.comp contDiff_snd.contDiffOn fun _ hq => hq.2

theorem velocity_smooth : ContDiffOn ℝ ∞ (↿h.vel) (univ ×ˢ Ici 0) := by
  have hL : ContDiffOn ℝ ∞ (fun q : ℝ³ × ℝ => ev V (σ₀ / 2) q.1) (univ ×ˢ Ici 0) :=
    ((contDiff_ev h.half_pos).comp contDiff_fst).contDiffOn
  exact re3.contDiff.comp_contDiffOn (hL.clm_apply h.contDiffOn_w_snd)

theorem pressure_smooth : ContDiffOn ℝ ∞ (↿h.prs) (univ ×ˢ Ici 0) := by
  set B := presOp (σ₀ / 2) (σ₀ / 4) h.half_pos.le h.quarter_le
  have hB : ContDiffOn ℝ ∞ (fun q : ℝ³ × ℝ => (B.bilinearRestrictScalars ℝ) (h.w q.2))
      (univ ×ˢ Ici 0) :=
    (B.bilinearRestrictScalars ℝ).contDiff.comp_contDiffOn h.contDiffOn_w_snd
  have hq : ContDiffOn ℝ ∞ (fun q : ℝ³ × ℝ => B (h.w q.2) (h.w q.2)) (univ ×ˢ Ici 0) :=
    hB.clm_apply h.contDiffOn_w_snd
  have hL : ContDiffOn ℝ ∞ (fun q : ℝ³ × ℝ => ev ℂ (σ₀ / 4) q.1) (univ ×ˢ Ici 0) :=
    ((contDiff_ev h.quarter_pos).comp contDiff_fst).contDiffOn
  exact Complex.reCLM.contDiff.comp_contDiffOn (hL.clm_apply hq)

/-! ### Initial datum and periodicity -/

theorem initial_condition (x : ℝ³) : h.vel x 0 = datum σ₀ a x := by
  rw [vel_eq, datum]
  congr 2
  funext k
  exact h.coef_zero_time k

theorem vel_periodic (t : ℝ) : IsOnePeriodic (fun x => h.vel x t) := fun x i => by
  simp only [vel, ev_add_single]

theorem prs_periodic (t : ℝ) : IsOnePeriodic (fun x => h.prs x t) := fun x i => by
  simp only [prs, ev_add_single]

/-! ### The time derivative -/

theorem tq_lt : σ₀ / 2 < 3 * σ₀ / 4 := by linarith [h.weight]
theorem tq_le : 3 * σ₀ / 4 ≤ σ₀ := by linarith [h.weight]
theorem tq_nn : 0 ≤ 3 * σ₀ / 4 := by linarith [h.weight]

/-- The derivative of the solution curve (weight `σ₀ / 2`). -/
noncomputable def W' (t : ℝ) : D :=
  curveDeriv ν σ₀ (σ₀ / 2) (3 * σ₀ / 4) h.pos.le h.tq_lt h.tq_le h.tq_nn h.sol t

/-- Physical Fourier coefficients of `∂ₜ u`. -/
noncomputable def dcoefT (t : ℝ) (k : Λ) : V :=
  wt (-σ₀) k • (-(((ν * lam k : ℝ)) : ℂ) • h.sol k (Real.toNNReal t) +
    forcing σ₀ h.sol k (Real.toNNReal t))

theorem dcoefT_eq (t : ℝ) (k : Λ) : h.dcoefT t k = wt (-(σ₀ / 2)) k • h.W' t k := by
  rw [W', curveDeriv_apply h.sol_fix, dcoefT, wt_smul_wt_smul]
  congr 2; ring

theorem rapidDecay_dcoefT (t : ℝ) : RapidDecay (h.dcoefT t) := by
  have := rapidDecay_of_weighted h.half_pos (h.W' t)
  rwa [show (fun k => wt (-(σ₀ / 2)) k • h.W' t k) = h.dcoefT t from
    (funext (h.dcoefT_eq t)).symm] at this

theorem hasDerivWithinAt_vel (x : ℝ³) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun τ => h.vel x τ) (re3 (four (h.dcoefT t) x)) (Ici 0) t := by
  have hw : HasDerivWithinAt h.w (h.W' t) (Ici 0) t :=
    hasDerivWithinAt_curve h.sol_fix h.tq_lt h.tq_le h.tq_nn ht
  have hc := (re3.comp (ev V (σ₀ / 2) x)).hasFDerivAt.comp_hasDerivWithinAt t hw
  refine hc.congr_deriv ?_
  rw [ContinuousLinearMap.comp_apply, ev_apply h.half_pos]
  congr 2
  funext k
  exact (h.dcoefT_eq t k).symm

theorem derivWithin_vel (x : ℝ³) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin (fun τ => h.vel x τ) (Ici 0) t = re3 (four (h.dcoefT t) x) :=
  (h.hasDerivWithinAt_vel x ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

theorem vel_fun' (t : ℝ) : (fun x => h.vel x t) = fun x => re3 (four (h.coef t) x) :=
  funext fun x => h.vel_eq x t

/-! ### The pressure -/

/-- The pressure coefficients read at weight `σ₀ / 4`. -/
noncomputable def pres (t : ℝ) : Dsc :=
  presOp (σ₀ / 2) (σ₀ / 4) h.half_pos.le h.quarter_le (h.w t) (h.w t)

theorem pcoef_eq (t : ℝ) (n : Λ) : h.pcoef t n = wt (-(σ₀ / 4)) n • h.pres t n := by
  rw [pres, presOp_apply, pcoef, smul_eq_mul, ← tsum_mul_left]
  congr 1
  funext j
  simp only [w, curve_apply, coef, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have key : wt (-(σ₀ / 4)) n * (wt (σ₀ / 4) n * wt (-(σ₀ / 2)) j * wt (-(σ₀ / 2)) (n - j)) *
      (wt (σ₀ / 2 - σ₀) j * wt (σ₀ / 2 - σ₀) (n - j)) = wt (-σ₀) j * wt (-σ₀) (n - j) := by
    simp only [wt, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2; ring
  linear_combination (-(pm n (h.sol j (Real.toNNReal t)) (h.sol (n - j) (Real.toNNReal t)))) * key

theorem rapidDecay_pcoef (t : ℝ) : RapidDecay (h.pcoef t) := by
  have := rapidDecay_of_weighted h.quarter_pos (h.pres t)
  rwa [show (fun n => wt (-(σ₀ / 4)) n • h.pres t n) = h.pcoef t from
    (funext (h.pcoef_eq t)).symm] at this

theorem prs_fun (t : ℝ) : (fun x => h.prs x t) = fun x => (four (h.pcoef t) x).re := by
  funext x
  rw [prs, ev_apply h.quarter_pos]
  congr 2
  funext n
  exact (h.pcoef_eq t n).symm

/-! ### The convective term -/

theorem norm_coef_le' (t : ℝ) (j : Λ) : ‖h.coef t j‖ ≤ Real.exp (-σ₀ * kn j) * ‖h.sol j‖ := by
  rw [coef, norm_smul, norm_wt]
  exact mul_le_mul_of_nonneg_left ((h.sol j).norm_coe_le_norm _) (Real.exp_pos _).le

theorem norm_coef_mul_le (t : ℝ) (n j : Λ) :
    ‖h.coef t j‖ * ‖h.coef t (n - j)‖ ≤ Real.exp (-σ₀ * kn n) * (‖h.sol‖ * ‖h.sol j‖) := by
  have h1 := h.norm_coef_le' t j
  have h2 := h.norm_coef_le t (n - j)
  have h3 : Real.exp (-σ₀ * kn j) * Real.exp (-σ₀ * kn (n - j)) ≤ Real.exp (-σ₀ * kn n) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have := kn_le_add_sub n j
    have := h.weight
    nlinarith
  calc ‖h.coef t j‖ * ‖h.coef t (n - j)‖
      ≤ (Real.exp (-σ₀ * kn j) * ‖h.sol j‖) * (Real.exp (-σ₀ * kn (n - j)) * ‖h.sol‖) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = (Real.exp (-σ₀ * kn j) * Real.exp (-σ₀ * kn (n - j))) * (‖h.sol‖ * ‖h.sol j‖) := by ring
    _ ≤ Real.exp (-σ₀ * kn n) * (‖h.sol‖ * ‖h.sol j‖) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)

theorem hasSum_bnd (n : Λ) :
    HasSum (fun j => Real.exp (-σ₀ * kn n) * (‖h.sol‖ * ‖h.sol j‖))
      (Real.exp (-σ₀ * kn n) * (‖h.sol‖ * ‖h.sol‖)) := by
  have := ((l1_summable h.sol).hasSum.mul_left ‖h.sol‖).mul_left (Real.exp (-σ₀ * kn n))
  rwa [← l1_norm_eq] at this

/-- Fourier coefficients of the convective term `(u · ∇) u`. -/
noncomputable def Qc (t : ℝ) (n : Λ) : V :=
  ∑' j, (2 * π * I * ⟪kC n, h.coef t j⟫_ℂ) • h.coef t (n - j)

theorem norm_Qc_summand_le (t : ℝ) (n j : Λ) :
    ‖(2 * π * I * ⟪kC n, h.coef t j⟫_ℂ) • h.coef t (n - j)‖ ≤
      2 * π * kn n * (Real.exp (-σ₀ * kn n) * (‖h.sol‖ * ‖h.sol j‖)) := by
  rw [norm_smul, norm_mul, norm_two_pi_I]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (kC n) (h.coef t j)
  rw [norm_kC] at h1
  have h2 := h.norm_coef_mul_le t n j
  have hk := kn_nonneg n
  calc 2 * π * ‖⟪kC n, h.coef t j⟫_ℂ‖ * ‖h.coef t (n - j)‖
      ≤ 2 * π * (kn n * ‖h.coef t j‖) * ‖h.coef t (n - j)‖ := by gcongr
    _ = 2 * π * kn n * (‖h.coef t j‖ * ‖h.coef t (n - j)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem summable_Qc (t : ℝ) (n : Λ) :
    Summable fun j => (2 * π * I * ⟪kC n, h.coef t j⟫_ℂ) • h.coef t (n - j) :=
  Summable.of_norm_bounded ((h.hasSum_bnd n).summable.mul_left (2 * π * kn n))
    (h.norm_Qc_summand_le t n)

theorem norm_Qc_le (t : ℝ) (n : Λ) :
    ‖h.Qc t n‖ ≤ 2 * π * kn n * (Real.exp (-σ₀ * kn n) * (‖h.sol‖ * ‖h.sol‖)) :=
  tsum_of_norm_bounded ((h.hasSum_bnd n).mul_left (2 * π * kn n)) (h.norm_Qc_summand_le t n)

theorem rapidDecay_Qc (t : ℝ) : RapidDecay (h.Qc t) := fun m =>
  ((summable_pow_mul_exp_neg_kn (m + 1) h.weight).mul_left
      (2 * π * (‖h.sol‖ * ‖h.sol‖))).of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (kn_nonneg k) m) (norm_nonneg _)) fun k => by
      calc kn k ^ m * ‖h.Qc t k‖
          ≤ kn k ^ m * (2 * π * kn k * (Real.exp (-σ₀ * kn k) * (‖h.sol‖ * ‖h.sol‖))) :=
            mul_le_mul_of_nonneg_left (h.norm_Qc_le t k) (pow_nonneg (kn_nonneg k) m)
        _ = 2 * π * (‖h.sol‖ * ‖h.sol‖) * (kn k ^ (m + 1) * Real.exp (-σ₀ * kn k)) := by ring

theorem Lk_vel (x : ℝ³) (t : ℝ) (k : Λ) :
    Lk k (h.vel x t) = 2 * π * I * ⟪kC k, four (h.coef t) x⟫_ℂ := by
  rw [Lk_apply, ← h.ofReal3_vel x t, inner_kC_ofReal3]

theorem convective_eq (x : ℝ³) (t : ℝ) :
    fderiv ℝ (fun y => h.vel y t) x (h.vel x t) = re3 (four (h.Qc t) x) := by
  rw [h.vel_fun' t, fderiv_re3_four (h.rapidDecay_coef t)]
  simp only [h.Lk_vel x t]
  rw [four_convective x (h.rapidDecay_coef t) (h.coef_div t)]
  rfl

/-! ### The coefficient identity -/

theorem inner_kC_Qc (t : ℝ) (n : Λ) :
    ⟪kC n, h.Qc t n⟫_ℂ =
      2 * π * I * ∑' j, ⟪kC n, h.coef t j⟫_ℂ * ⟪kC n, h.coef t (n - j)⟫_ℂ := by
  rw [Qc, ← innerSL_apply_apply, (innerSL ℂ (kC n)).map_tsum (h.summable_Qc t n),
    ← tsum_mul_left]
  congr 1
  funext j
  rw [innerSL_apply_apply, inner_smul_right]
  ring

theorem pcoef_eq_sum (t : ℝ) (n : Λ) :
    h.pcoef t n = -(((kn n ^ 2 : ℝ) : ℂ)⁻¹) *
      ∑' j, ⟪kC n, h.coef t j⟫_ℂ * ⟪kC n, h.coef t (n - j)⟫_ℂ := by
  rw [pcoef, ← tsum_mul_left]
  simp only [pm_apply]

theorem forcing_eq (t : ℝ) (n : Λ) :
    wt (-σ₀) n • forcing σ₀ h.sol n (Real.toNNReal t) = -leray n (h.Qc t n) := by
  rw [forcing, Qc, (leray n).map_tsum (h.summable_Qc t n), ← tsum_neg, ← tsum_const_smul'']
  congr 1
  funext j
  simp only [nl_apply, coef, map_smul, smul_smul, inner_smul_right, ratio_eq_wt]
  rw [← neg_smul]
  congr 1
  have hw : wt (-σ₀) n * wt σ₀ n = 1 := by rw [wt_mul]; simp [wt]
  linear_combination (-(2 * π * I) * wt (-σ₀) j * wt (-σ₀) (n - j) *
    ⟪kC n, h.sol j (Real.toNNReal t)⟫_ℂ) * hw

theorem dcoefT_eq_leray (t : ℝ) (n : Λ) :
    h.dcoefT t n = -(((ν * lam n : ℝ)) : ℂ) • h.coef t n - leray n (h.Qc t n) := by
  rw [dcoefT, smul_add, h.forcing_eq, coef,
    smul_comm (wt (-σ₀) n) (-(((ν * lam n : ℝ)) : ℂ)), sub_eq_add_neg]

/-- The Navier–Stokes equation, mode by mode, tested against a real vector `e`. -/
theorem coef_identity (t : ℝ) (e : ℝ³) (n : Λ) :
    ⟪ofReal3 e, h.dcoefT t n⟫_ℂ + ⟪ofReal3 e, h.Qc t n⟫_ℂ +
      ((ν * lam n : ℝ) : ℂ) * ⟪ofReal3 e, h.coef t n⟫_ℂ + Lk n e * h.pcoef t n = 0 := by
  rw [h.dcoefT_eq_leray, leray_apply, norm_kC, h.inner_kC_Qc, h.pcoef_eq_sum, Lk_apply]
  simp only [inner_sub_right, inner_smul_right, inner_ofReal3_kC]
  ring

/-! ### The equations -/

theorem ns_eq (x : ℝ³) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin (fun τ => h.vel x τ) (Ici 0) t + fderiv ℝ (fun y => h.vel y t) x (h.vel x t) =
      ν • Δ (fun y => h.vel y t) x - gradient (fun y => h.prs y t) x := by
  rw [h.derivWithin_vel x ht, h.convective_eq x t, h.vel_fun' t,
    laplacian_re3_four (h.rapidDecay_coef t)]
  refine ext_inner_right ℝ fun e => ?_
  rw [inner_add_left, inner_sub_left, real_inner_smul_left, inner_gradient_eq, h.prs_fun t,
    fderiv_re_four (h.rapidDecay_pcoef t)]
  simp only [← re_inner_ofReal3]
  rw [inner_four (h.rapidDecay_dcoefT t), inner_four (h.rapidDecay_Qc t),
    inner_four (h.rapidDecay_coef t).lap]
  have hγ := ((h.rapidDecay_coef t).lap).inner (ofReal3 e)
  have hβ := (h.rapidDecay_Qc t).inner (ofReal3 e)
  have hδ : RapidDecay fun n => Lk n e * h.pcoef t n :=
    (h.rapidDecay_pcoef t).of_norm_le_pow (2 * π * ‖e‖) 1 fun n => by
      rw [norm_mul]
      calc ‖Lk n e‖ * ‖h.pcoef t n‖ ≤ 2 * π * kn n * ‖e‖ * ‖h.pcoef t n‖ :=
            mul_le_mul_of_nonneg_right (norm_Lk_apply_le n e) (norm_nonneg _)
        _ = 2 * π * ‖e‖ * (kn n ^ 1 * ‖h.pcoef t n‖) := by ring
  have hα : four (fun k => ⟪ofReal3 e, h.dcoefT t k⟫_ℂ) x =
      four (fun k => (ν : ℂ) * ⟪ofReal3 e, (-((4 * π ^ 2 * kn k ^ 2 : ℝ) : ℂ)) • h.coef t k⟫_ℂ -
        ⟪ofReal3 e, h.Qc t k⟫_ℂ - Lk k e * h.pcoef t k) x := by
    congr 1
    funext k
    have hk := h.coef_identity t e k
    rw [inner_smul_right]
    simp only [lam] at hk
    push_cast at hk ⊢
    linear_combination hk
  rw [hα, four_lin hγ hβ hδ, Complex.sub_re, Complex.sub_re, Complex.re_ofReal_mul]
  ring

theorem div_free (x : ℝ³) (t : ℝ) : divergence (fun y => h.vel y t) x = 0 := by
  rw [h.vel_fun' t]
  exact divergence_re3_four (h.rapidDecay_coef t) (h.coef_div t) x

/-! ### The datum -/

theorem rapidDecay_datum : RapidDecay fun k => wt (-σ₀) k • a k :=
  rapidDecay_of_weighted h.weight a

theorem initialVelocityConditionPeriodic : InitialVelocityConditionPeriodic (datum σ₀ a) where
  div_free x := divergence_re3_four h.rapidDecay_datum
    (fun k => by rw [inner_smul_right, h.div k, mul_zero]) x
  smooth := re3.contDiff.comp (contDiff_four h.rapidDecay_datum)
  isOnePeriodic x i := by simp only [datum, four_add_single]

/-! ### The solution -/

/-- **Global existence and smoothness for small analytic periodic data.** -/
theorem existencePeriodic :
    NavierStokesExistenceAndSmoothnessPeriodic ν (datum σ₀ a) 0 h.vel h.prs where
  navier_stokes x t ht := by
    simp only [Pi.zero_apply, add_zero]
    exact h.ns_eq x ht
  div_free x t _ := h.div_free x t
  initial_condition := h.initial_condition
  velocity_smooth := h.velocity_smooth
  pressure_smooth := h.pressure_smooth
  isOnePeriodic_velocity t _ := h.vel_periodic t
  isOnePeriodic_pressure t _ := h.prs_periodic t

end Small

/-! ### The statement in terms of Fourier coefficients -/

/-- **Small analytic data.** Let `u₀(x) = Re Σₖ c_k e^{2πi k·x}` with divergence-free Hermitian
coefficients satisfying `Σₖ e^{σ|k|} |c_k| ≤ πν/4` for some `σ > 0`. Then `u₀` is an admissible
periodic datum, and the unforced Navier–Stokes equations with viscosity `ν > 0` have a global
smooth periodic solution with this datum, in the exact sense of the Clay/Formal Conjectures
statement (B). -/
theorem existencePeriodic_of_small {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (c : Λ → V)
    (hsum : Summable fun k => Real.exp (σ * kn k) * ‖c k‖)
    (hsmall : ∑' k, Real.exp (σ * kn k) * ‖c k‖ ≤ π * ν / 4)
    (hdiv : ∀ k, ⟪kC k, c k⟫_ℂ = 0) (hherm : ∀ k, c (-k) = vconj (c k)) :
    InitialVelocityConditionPeriodic (fun x => re3 (four c x)) ∧
      ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic ν (fun x => re3 (four c x)) 0 v p := by
  have hn : ∀ k, ‖wt σ k • c k‖ = Real.exp (σ * kn k) * ‖c k‖ := fun k => by
    rw [norm_smul, norm_wt]
  let a : D := ⟨fun k => wt σ k • c k, memℓp_one_of_summable (by simpa only [hn] using hsum)⟩
  have ha : ∀ k, a k = wt σ k • c k := fun k => rfl
  have hS : Small ν σ a :=
    { pos := hν
      weight := hσ
      small := by rw [l1_norm_eq]; simpa only [ha, hn] using hsmall
      div := fun k => by rw [ha, inner_smul_right, hdiv, mul_zero]
      herm := fun k => by rw [ha, ha, wt, wt, kn_neg, hherm, vconj_ofReal_smul] }
  have hd : Small.datum σ a = fun x => re3 (four c x) := by
    funext x
    rw [Small.datum]
    congr 2
    funext k
    rw [ha, wt_smul_wt_smul, neg_add_cancel]
    simp [wt]
  rw [← hd]
  exact ⟨hS.initialVelocityConditionPeriodic, hS.vel, hS.prs, hS.existencePeriodic⟩

theorem rapidDecay_of_summable_exp {σ : ℝ} (hσ : 0 < σ) {c : Λ → V}
    (hsum : Summable fun k => Real.exp (σ * kn k) * ‖c k‖) : RapidDecay c := fun m => by
  obtain ⟨C, hC⟩ := pow_mul_exp_neg_le m hσ
  refine (hsum.mul_left C).of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (kn_nonneg k) m) (norm_nonneg _)) fun k => ?_
  have h1 : Real.exp (-σ * kn k) * Real.exp (σ * kn k) = 1 := by
    rw [← Real.exp_add]; simp
  calc kn k ^ m * ‖c k‖
      = (kn k ^ m * Real.exp (-σ * kn k)) * (Real.exp (σ * kn k) * ‖c k‖) := by
        linear_combination (-(kn k ^ m * ‖c k‖)) * h1
    _ ≤ C * (Real.exp (σ * kn k) * ‖c k‖) :=
        mul_le_mul_of_nonneg_right (hC (kn k) (kn_nonneg k)) (by positivity)

theorem re3_four_smul (ε : ℝ) {c : Λ → V} (hc : RapidDecay c) (x : ℝ³) :
    re3 (four (fun k => (ε : ℂ) • c k) x) = ε • re3 (four c x) := by
  have := four_map ((ε : ℂ) • ContinuousLinearMap.id ℂ V) hc x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at this
  rw [← this]
  ext i
  simp

/-- **Every analytic datum, scaled down, has a global solution.** For any divergence-free
Hermitian coefficients with `Σₖ e^{σ|k|} |c_k| < ∞`, there is `ε₀ > 0` such that for `|ε| ≤ ε₀`
the unforced problem (B) with datum `ε · Re Σₖ c_k e^{2πi k·x}` has a global smooth solution. -/
theorem existencePeriodic_of_analytic {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (c : Λ → V)
    (hsum : Summable fun k => Real.exp (σ * kn k) * ‖c k‖)
    (hdiv : ∀ k, ⟪kC k, c k⟫_ℂ = 0) (hherm : ∀ k, c (-k) = vconj (c k)) :
    ∃ ε₀ > 0, ∀ ε : ℝ, |ε| ≤ ε₀ →
      ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic ν (fun x => ε • re3 (four c x)) 0 v p := by
  set S := ∑' k, Real.exp (σ * kn k) * ‖c k‖ with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun k => by positivity
  have hpν : 0 < π * ν / 4 := by positivity
  refine ⟨π * ν / 4 / (S + 1), by positivity, fun ε hε => ?_⟩
  have hn : ∀ k, Real.exp (σ * kn k) * ‖(ε : ℂ) • c k‖ = |ε| * (Real.exp (σ * kn k) * ‖c k‖) :=
    fun k => by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]; ring
  have hsum' : Summable fun k => Real.exp (σ * kn k) * ‖(ε : ℂ) • c k‖ := by
    simpa only [hn] using hsum.mul_left |ε|
  have hsmall' : ∑' k, Real.exp (σ * kn k) * ‖(ε : ℂ) • c k‖ ≤ π * ν / 4 := by
    simp only [hn]
    rw [tsum_mul_left, ← hSdef]
    calc |ε| * S ≤ π * ν / 4 / (S + 1) * S := mul_le_mul_of_nonneg_right hε hS0
      _ ≤ π * ν / 4 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
  obtain ⟨-, v, p, hvp⟩ := existencePeriodic_of_small hν hσ (fun k => (ε : ℂ) • c k) hsum'
    hsmall' (fun k => by simp only [inner_smul_right, hdiv, mul_zero])
    (fun k => by simp only [hherm, vconj_ofReal_smul])
  refine ⟨v, p, ?_⟩
  have : (fun x => re3 (four (fun k => (ε : ℂ) • c k) x)) = fun x => ε • re3 (four c x) :=
    funext fun x => re3_four_smul ε (rapidDecay_of_summable_exp hσ hsum) x
  rwa [this] at hvp

/-- **Large viscosity.** For any analytic divergence-free Hermitian coefficients there is `ν₀`
such that (B) holds for the datum `Re Σₖ c_k e^{2πi k·x}` at every viscosity `ν ≥ ν₀`. -/
theorem existencePeriodic_of_large_viscosity {σ : ℝ} (hσ : 0 < σ) (c : Λ → V)
    (hsum : Summable fun k => Real.exp (σ * kn k) * ‖c k‖)
    (hdiv : ∀ k, ⟪kC k, c k⟫_ℂ = 0) (hherm : ∀ k, c (-k) = vconj (c k)) :
    ∃ ν₀ > 0, ∀ ν ≥ ν₀,
      ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic ν (fun x => re3 (four c x)) 0 v p := by
  set S := ∑' k, Real.exp (σ * kn k) * ‖c k‖
  have hS0 : 0 ≤ S := tsum_nonneg fun k => by positivity
  refine ⟨4 * S / π + 1, by positivity, fun ν hν => ?_⟩
  have hν0 : 0 < ν := lt_of_lt_of_le (by positivity) hν
  have hsmall : S ≤ π * ν / 4 := by
    have h1 : 4 * S / π ≤ ν := by linarith
    rw [div_le_iff₀ pi_pos] at h1
    linarith
  exact (existencePeriodic_of_small hν0 hσ c hsum hsmall hdiv hherm).2

end NavierStokesAB.SmallData
