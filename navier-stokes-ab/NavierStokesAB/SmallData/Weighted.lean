import NavierStokesAB.SmallData.FixedPoint

/-!
# Weighted coefficient spaces and the operators between them

An element `w ∈ D = ℓ¹(Λ, ℂ³)` read "at weight `s`" stands for the physical coefficients
`e^{-s|k|} w k`. Changing the weight, applying the Laplacian symbol, or applying the nonlinearity
loses a little weight, and each of these is a bounded operator `D → D` once the target weight is
strictly smaller:

* `shift s s'` (`s' ≤ s`): the same physical sequence, read at weight `s'`;
* `lapOp ν s s'` (`s' < s`): `c ↦ -ν λ_k c_k`;
* `nlOp s s'` (`s' < s`): `(c, c') ↦ Σⱼ nl_k (c j) (c' (k - j))`.

`slice σ₀ s t` reads the solution `b ∈ X` (weight `σ₀`) at time `t` and weight `s ≤ σ₀`;
it is continuous in `t`.
-/

open Real Complex Metric Set Filter Topology
open scoped NNReal BoundedContinuousFunction InnerProductSpace

-- Instance search over operator spaces on these concrete spaces is slow.
set_option synthInstance.maxHeartbeats 200000

namespace NavierStokesAB.SmallData

/-- `e^{s|k|}` as a complex number. -/
noncomputable def wt (s : ℝ) (k : Λ) : ℂ := (Real.exp (s * kn k) : ℂ)

theorem norm_wt (s : ℝ) (k : Λ) : ‖wt s k‖ = Real.exp (s * kn k) := by
  rw [wt, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem wt_mul (s s' : ℝ) (k : Λ) : wt s k * wt s' k = wt (s + s') k := by
  simp only [wt, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2; ring

@[simp] theorem wt_zero (k : Λ) : wt 0 k = 1 := by simp [wt]

theorem norm_wt_le_one {s : ℝ} (hs : s ≤ 0) (k : Λ) : ‖wt s k‖ ≤ 1 := by
  rw [norm_wt, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg hs (kn_nonneg k)

/-! ### Diagonal multipliers -/

noncomputable instance : NormedAddCommGroup (V →L[ℂ] V) := inferInstance
noncomputable instance : NormedSpace ℂ (V →L[ℂ] V) := inferInstance
noncomputable instance : NormedAddCommGroup (D →L[ℂ] D) := inferInstance
noncomputable instance : NormedSpace ℂ (D →L[ℂ] D) := inferInstance

theorem diag_summable (m : Λ → ℂ) {C : ℝ} (hm : ∀ k, ‖m k‖ ≤ C) (w : D) :
    Summable fun k => ‖m k • w k‖ :=
  ((l1_summable w).mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) fun k => by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hm k) (norm_nonneg _)

/-- The diagonal multiplier `w ↦ (m k • w k)`. -/
noncomputable def diag (m : Λ → ℂ) {C : ℝ} (hm : ∀ k, ‖m k‖ ≤ C) : D →L[ℂ] D :=
  LinearMap.mkContinuous
    { toFun := fun w => ⟨fun k => m k • w k, memℓp_one_of_summable (diag_summable m hm w)⟩
      map_add' := fun w w' => lp.ext (funext fun k => by
        show m k • (w + w') k = m k • w k + m k • w' k
        simp [smul_add])
      map_smul' := fun c w => lp.ext (funext fun k => by
        show m k • (c • w) k = c • (m k • w k)
        simp [smul_comm (m k) c]) }
    C fun w => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [l1_norm_eq, l1_norm_eq, ← tsum_mul_left]
      exact Summable.tsum_le_tsum (fun k => by
        show ‖m k • w k‖ ≤ C * ‖w k‖
        rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hm k) (norm_nonneg _))
        (diag_summable m hm w) ((l1_summable w).mul_left C)

theorem diag_apply (m : Λ → ℂ) {C : ℝ} (hm : ∀ k, ‖m k‖ ≤ C) (w : D) (k : Λ) :
    diag m hm w k = m k • w k := rfl

/-! ### Weight shifts, the Laplacian symbol and the nonlinearity -/

/-- Read a coefficient sequence at a smaller weight. -/
noncomputable def shift (s s' : ℝ) (h : s' ≤ s) : D →L[ℂ] D :=
  diag (fun k => wt (s' - s) k) (C := 1) fun k => norm_wt_le_one (by linarith) k

theorem shift_apply (s s' : ℝ) (h : s' ≤ s) (w : D) (k : Λ) :
    shift s s' h w k = wt (s' - s) k • w k := rfl

/-- `sup_r r^m e^{-ε r}`, as provided by `pow_mul_exp_neg_le`. -/
noncomputable def powExpBound (m : ℕ) {ε : ℝ} (hε : 0 < ε) : ℝ :=
  Classical.choose (pow_mul_exp_neg_le m hε)

theorem powExpBound_spec (m : ℕ) {ε : ℝ} (hε : 0 < ε) (r : ℝ) (hr : 0 ≤ r) :
    r ^ m * Real.exp (-ε * r) ≤ powExpBound m hε :=
  Classical.choose_spec (pow_mul_exp_neg_le m hε) r hr

theorem powExpBound_nonneg (m : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 ≤ powExpBound m hε :=
  le_trans (by positivity) (powExpBound_spec m hε 0 le_rfl)

/-- The heat symbol `-ν λ_k`, with a loss of weight. -/
noncomputable def lapOp (ν s s' : ℝ) (hν : 0 ≤ ν) (h : s' < s) : D →L[ℂ] D :=
  diag (fun k => (((-(ν * lam k)) : ℝ) : ℂ) * wt (s' - s) k)
    (C := ν * (4 * π ^ 2) * powExpBound 2 (sub_pos.2 h)) fun k => by
      rw [norm_mul, norm_wt, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (mul_nonneg hν (lam_nonneg k))]
      have := powExpBound_spec 2 (sub_pos.2 h) (kn k) (kn_nonneg k)
      unfold lam
      have hexp : Real.exp ((s' - s) * kn k) = Real.exp (-(s - s') * kn k) := by ring_nf
      rw [hexp]
      calc ν * (4 * π ^ 2 * kn k ^ 2) * Real.exp (-(s - s') * kn k)
          = ν * (4 * π ^ 2) * (kn k ^ 2 * Real.exp (-(s - s') * kn k)) := by ring
        _ ≤ ν * (4 * π ^ 2) * powExpBound 2 (sub_pos.2 h) := by gcongr

theorem lapOp_apply (ν s s' : ℝ) (hν : 0 ≤ ν) (h : s' < s) (w : D) (k : Λ) :
    lapOp ν s s' hν h w k = ((((-(ν * lam k)) : ℝ) : ℂ) * wt (s' - s) k) • w k := rfl

/-- The symbol of the nonlinearity from weight `s` to weight `s'`. -/
noncomputable def nlOpSymbol (s s' : ℝ) (hs : 0 ≤ s) (h : s' < s) : Symbol V V where
  K k j := (wt s' k * wt (-s) j * wt (-s) (k - j)) • nl k
  C := 2 * π * powExpBound 1 (sub_pos.2 h)
  C_nonneg := by have := powExpBound_nonneg 1 (sub_pos.2 h); positivity
  bound k j := by
    rw [norm_smul, norm_mul, norm_mul, norm_wt, norm_wt, norm_wt, ← Real.exp_add, ← Real.exp_add]
    have htri := kn_le_add_sub k j
    have hexp : Real.exp (s' * kn k + -s * kn j + -s * kn (k - j)) ≤
        Real.exp (-(s - s') * kn k) := by
      apply Real.exp_le_exp.2
      nlinarith [mul_nonneg hs (sub_nonneg.2 htri)]
    have hb := powExpBound_spec 1 (sub_pos.2 h) (kn k) (kn_nonneg k)
    calc Real.exp (s' * kn k + -s * kn j + -s * kn (k - j)) * ‖nl k‖
        ≤ Real.exp (-(s - s') * kn k) * (2 * π * kn k) :=
          mul_le_mul hexp (norm_nl_le k) (norm_nonneg _) (Real.exp_pos _).le
      _ = 2 * π * (kn k ^ 1 * Real.exp (-(s - s') * kn k)) := by ring
      _ ≤ 2 * π * powExpBound 1 (sub_pos.2 h) := by gcongr

/-- The nonlinearity `(c, c') ↦ Σⱼ nl_k (c j) (c' (k - j))`, from weight `s` to weight `s'`. -/
noncomputable def nlOp (s s' : ℝ) (hs : 0 ≤ s) (h : s' < s) : D →L[ℂ] D →L[ℂ] D :=
  convCLM (nlOpSymbol s s' hs h)

theorem nlOp_apply (s s' : ℝ) (hs : 0 ≤ s) (h : s' < s) (w w' : D) (k : Λ) :
    nlOp s s' hs h w w' k =
      ∑' j, (wt s' k * wt (-s) j * wt (-s) (k - j)) • nl k (w j) (w' (k - j)) := by
  simp [nlOp, nlOpSymbol]

/-! ### Reading the solution at a time and a weight -/

section Slice

theorem slice_summable (σ₀ s : ℝ) (hs : s ≤ σ₀) (b : X) (t : ℝ≥0) :
    Summable fun k => ‖wt (s - σ₀) k • b k t‖ :=
  (l1_summable b).of_nonneg_of_le (fun _ => norm_nonneg _) fun k => by
    rw [norm_smul]
    calc ‖wt (s - σ₀) k‖ * ‖b k t‖ ≤ 1 * ‖b k‖ :=
          mul_le_mul (norm_wt_le_one (by linarith) k) ((b k).norm_coe_le_norm t)
            (norm_nonneg _) zero_le_one
      _ = ‖b k‖ := one_mul _

/-- The solution at time `t`, read at weight `s`. -/
noncomputable def sliceFun (σ₀ s : ℝ) (hs : s ≤ σ₀) (b : X) (t : ℝ≥0) : D :=
  ⟨fun k => wt (s - σ₀) k • b k t, memℓp_one_of_summable (slice_summable σ₀ s hs b t)⟩

theorem sliceFun_apply (σ₀ s : ℝ) (hs : s ≤ σ₀) (b : X) (t : ℝ≥0) (k : Λ) :
    sliceFun σ₀ s hs b t k = wt (s - σ₀) k • b k t := rfl

theorem norm_sliceFun_sub_le (σ₀ s : ℝ) (hs : s ≤ σ₀) (b : X) (t t₀ : ℝ≥0) :
    ‖sliceFun σ₀ s hs b t - sliceFun σ₀ s hs b t₀‖ ≤ ∑' k, ‖b k t - b k t₀‖ := by
  have hsum : Summable fun k => ‖b k t - b k t₀‖ :=
    ((l1_summable b).mul_left 2).of_nonneg_of_le (fun _ => norm_nonneg _) fun k => by
      calc ‖b k t - b k t₀‖ ≤ ‖b k t‖ + ‖b k t₀‖ := norm_sub_le _ _
        _ ≤ ‖b k‖ + ‖b k‖ := add_le_add ((b k).norm_coe_le_norm t) ((b k).norm_coe_le_norm t₀)
        _ = 2 * ‖b k‖ := by ring
  rw [l1_norm_eq]
  refine Summable.tsum_le_tsum (fun k => ?_) (l1_summable _) hsum
  simp only [lp.coeFn_sub, Pi.sub_apply, sliceFun_apply, ← smul_sub, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_wt_le_one (by linarith) k)

theorem continuous_sliceFun (σ₀ s : ℝ) (hs : s ≤ σ₀) (b : X) :
    Continuous (sliceFun σ₀ s hs b) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hφ : Continuous fun t : ℝ≥0 => ∑' k, ‖b k t - b k t₀‖ :=
    continuous_tsum (fun k => ((b k).continuous.sub continuous_const).norm)
      ((l1_summable b).mul_left 2) fun k t => by
        calc ‖‖b k t - b k t₀‖‖ = ‖b k t - b k t₀‖ := norm_norm _
          _ ≤ ‖b k t‖ + ‖b k t₀‖ := norm_sub_le _ _
          _ ≤ ‖b k‖ + ‖b k‖ :=
              add_le_add ((b k).norm_coe_le_norm t) ((b k).norm_coe_le_norm t₀)
          _ = 2 * ‖b k‖ := by ring
  have h0 : (∑' k, ‖b k t₀ - b k t₀‖) = 0 := by simp
  have ht : Tendsto (fun t : ℝ≥0 => ∑' k, ‖b k t - b k t₀‖) (𝓝 t₀) (𝓝 0) := by
    rw [← h0]; exact hφ.tendsto t₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun t => norm_sliceFun_sub_le σ₀ s hs b t t₀) ht

end Slice

end NavierStokesAB.SmallData
