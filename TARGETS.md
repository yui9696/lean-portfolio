# ポートフォリオ用ターゲット(2026-08-19 裏取り済み)

方針: 研究内容は一切使わない。題材は Mathlib 公式の未形式化リスト
(https://leanprover-community.github.io/undergrad_todo.html)から選ぶ。
リストは自動生成で古いことがあるため、下記は **ローカルの mathlib ソース
(.lake/packages/mathlib)を grep して 2026-08-19 時点で本当に無いことを確認済み**。

## 第1目標【2026-08-19 完成 — sorry ゼロ・公理は標準3つのみ】
**実二次形式の同時対角化**(A 正定値・B 対称 ⟹ ∃P 可逆, PᵀAP=1 ∧ PᵀBP 対角)
- ファイル: `LeanPortfolio/SimultaneousDiagonalization.lean`(ビルド確認済み・sorry 1個)
- 既存部品: `Matrix.PosDef`(LinearAlgebra/Matrix/PosDef)、実スペクトル定理
  `Matrix.IsHermitian.spectral_theorem`(Analysis/Matrix/Spectrum)
- 近縁物: `Analysis/InnerProductSpace/JointEigenspace.lean` は「可換な自己随伴作用素の
  同時対角化」で別物(こちらは可換性不要・計量を取り替えるのが肝)
- 規模感: 1〜2週間。完成したら Mathlib PR 化(undergrad リスト掲載項目なので歓迎されやすい)

## 第2目標【2026-08-30 完成 — sorry ゼロ・公理は標準3つのみ】
**確率母関数 (PGF)** — `Mathlib/Probability/Moments/` に mgf/cgf はあるが PGF は皆無
(2026-08-30 の mathlib checkout 9d89974763 で複数の検索語により再確認)。
- ファイル: `LeanPortfolio/ProbabilityGeneratingFunction.lean`
- 完成内容: `pgf X μ t = μ[t ^ X]` の定義+基本 API(t=0/1 の値・非負性・[0,1] 上の単調性と
  有界性・[-1,1] 上の可積分性・a.e./IdentDistrib 合同)+冪級数表示 `pgf_eq_tsum`
  +**分布の一意性 `map_eq_map_of_pgf_eq`**(係数有界 ⟹ 収束半径 ≥ 1 ⟹
  `HasFPowerSeriesAt` の一意性で係数=点質量を回収)+独立和の積公式
  (`IndepFun.pgf_add`・`iIndepFun.pgf_sum`)
- 追加済(2026-08-30 第2便): mgf への橋 `pgf_exp_eq_mgf`+具体分布の閉形式
  (`ProbabilityGeneratingFunctionExamples.lean`: Poisson = exp(r(t−1)) 全実数 t・
  幾何分布 = p/(1−(1−p)t) on [−1,1])
- 追加済(2026-08-31): `hasFPowerSeriesAt_pgf`(0 の近傍で pgf = 点質量を係数とするべき級数)
  ・`analyticAt_pgf`・**`iteratedDeriv_pgf_zero`(n 階微分 @0 = n! · P(X=n))**。
  一意性定理はこれ経由に短縮。`HasFPowerSeriesOnBall.factorial_smul` + `coeff_ofScalars` で到達
  ⚠️`hasFPowerSeriesAt_pgf` は μ が結論にしか現れないので `obtain` では `(μ := μ)` が要る
- **★2026-09-01: 第1階乗モーメント(=平均)まで到達** `tendsto_deriv_pgf_nhdsLT_one`:
  X 可積分なら t→1⁻ で (pgf)'(t) → μ[X]。境界通過は Mathlib の Abel の定理
  `Real.tendsto_tsum_powerSeries_nhdsWithin_lt`(`Analysis/Complex/AbelLimit.lean`)。
  経路 = ①`hasSum_integral_comp`(∫f(X)を点質量の和にする一般補題・hasSum_pgf もこれから導出)
  ②`hasDerivAt_pgf`(|t|<1 での項別微分・`hasDerivAt_tsum_of_isPreconnected` を半径 (|t|+1)/2 の
  球上で使い M·n·r^(n-1) で優級数評価)③Abel を係数 n·P(X=n) に当て、
  **∑ n p_n x^n = x·(pgf)'(x) の恒等式で添字ずらしを回避**(x で割って終わり)
  ④`tendsto_pgf_nhdsLT_one`(左連続性)も同じ Abel から
- 未着手の残り: **第 n 階乗モーメント E[X(X−1)…(X−n+1)]**(n≥2)。1 階の議論を反復すれば
  出るはずだが、n 階導関数の級数表示を作る手間がある。値が ∞ の場合の扱いも設計が要る
- Mathlib PR 化する場合の置き場: `Mathlib/Probability/Moments/Generating.lean` 相当

## 第3候補(大物・単独では2週間で終わらない)
**ジョルダン標準形** — `JordanChevalley.lean`(半単純+冪零分解)はあるが標準形そのものは無い。
着手するなら第1目標完了後に、広義固有空間分解からの積み上げで部分 PR を刻む。

## 補足
- 部分分数分解は `Algebra/Polynomial/PartialFractions.lean` が既にあり(冪つき互いに素分解まで済み)、
  残るギャップは ℝ/ℂ での具体形と一意性のみ。見栄えの割に新規性が薄いので優先度下げ。
- 有限アーベル群のフーリエ変換: 巡回群 (`Analysis/Fourier/ZMod.lean`) はあるが一般有限アーベル群は
  未確認の可能性あり。第2候補の代替として調査価値あり。
