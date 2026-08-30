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
- 未着手の残り: 階乗モーメント(pgf の t=1 での微分)— MGFAnalytic 相当の解析機械が要るので
  次の刻みに
- Mathlib PR 化する場合の置き場: `Mathlib/Probability/Moments/Generating.lean` 相当

## 第3候補(大物・単独では2週間で終わらない)
**ジョルダン標準形** — `JordanChevalley.lean`(半単純+冪零分解)はあるが標準形そのものは無い。
着手するなら第1目標完了後に、広義固有空間分解からの積み上げで部分 PR を刻む。

## 補足
- 部分分数分解は `Algebra/Polynomial/PartialFractions.lean` が既にあり(冪つき互いに素分解まで済み)、
  残るギャップは ℝ/ℂ での具体形と一意性のみ。見栄えの割に新規性が薄いので優先度下げ。
- 有限アーベル群のフーリエ変換: 巡回群 (`Analysis/Fourier/ZMod.lean`) はあるが一般有限アーベル群は
  未確認の可能性あり。第2候補の代替として調査価値あり。
