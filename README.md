# Rocq Ltac Skills

[English](README.en.md) | 日本語

AIエージェントがRocq(旧 Coq)を用いた計算機科学の形式的証明(プログラム検証、形式意味論、型システム、エラー修復)を自律的に進めるためのスキル群。

## 特徴

- **形式的証明・計算機科学に特化**: 抽象数学ではなく、プログラミング言語の形式意味論(Operational Semantics)、型安全性(Progress / Preservation)、ステップ索引付け、コンパイラ正当性など、計算機科学・ソフトウェア検証(Software Foundations や CompCert 等のスタイル)に特化しています。
- **Pure Vanilla Ltac 100% 厳格準拠**: AIエージェントが最も陥りやすい SSReflect(`move=>`, `by []` 等)や Ltac2 との方言混同・構文汚染を、静的構文チェッカーおよびガイドラインにより徹底排除します。
- **Rocq REPLとの対話ループ**: `rocq repl` / `coqtop` サブプロセスと通信し、指定位置のゴール状態(Tactic State)や局所仮定を1手ずつ取得・検証可能です。QuickChick反例探索や型シグネチャ検索(Search)にも対応しています。
- **外部依存のないスクリプト**: 同梱スクリプトはPython 3の標準ライブラリのみで動作し、追加パッケージのインストールは不要です。
- **契約不変性と健全性監査**: エージェントによる定理シグネチャの無断改変や `admit` / `Admitted` の残留、未承認公理の混入を機械的に遮断する Soundness Gate を備えています。

## 前提条件・対応バージョン

| 項目                      | 想定・対応バージョン (Target)  | 動作検証済みバージョン (Verified)      | 備考                                                                |
| :------------------------ | :----------------------------- | :------------------------------------- | :------------------------------------------------------------------ |
| **Rocq Prover / Coq**     | `Rocq 9.0+` / `Coq 8.20+`      | `The Rocq Prover 9.1.0` (OCaml 4.14.2) | Rocq 9.0+ 名前空間(`From Stdlib`)および Coq 8.x(`From Coq`)の両対応 |
| **ビルドシステム / Dune** | `dune` (`>=3.10`), `rocq make` | Dune `3.21.0`                          | `_RocqProject` および `_CoqProject` の双方を自動検出                |
| **Python**                | `3.10` 以上                    | `3.14.7`                               | 標準ライブラリのみ使用(スクリプト同梱スキルのみ必要)                |

## スキル一覧

| スキル名                                                            | 役割                                                                                                         | 同梱スクリプト / リファレンス                                                                             |
| :------------------------------------------------------------------ | :----------------------------------------------------------------------------------------------------------- | :-------------------------------------------------------------------------------------------------------- |
| [`rocq-ltac-interactive-proof`](skills/rocq-ltac-interactive-proof) | `rocq repl` / `coqtop` と通信し、指定位置のゴール状態(Tactic State)を取得                                    | `scripts/rocq_goal.py`, `references/*.md`(3編)                                                            |
| [`rocq-ltac-proof-repair`](skills/rocq-ltac-proof-repair)           | インバージョン後の等式不整合やインデックス消失(`remember`)、終了性、Universe不整合など頻出エラーの診断と修復 | `references/*.md`(9編のエラー処方箋)                                                                      |
| [`rocq-ltac-syntax`](skills/rocq-ltac-syntax)                       | 証明構文リファレンスおよび高速構文チェック・SSReflect構文の混同防止                                          | `scripts/check_syntax.py`, `references/*.md`(5編)                                                         |
| [`rocq-ltac-cli`](skills/rocq-ltac-cli)                             | `rocq` / `coqc` / `dune` の運用自動化、ビルドログの構造化JSONパース、公理監査(Soundness Gate)                | `scripts/run_build.py`, `scripts/parse_diagnostics.py`, `scripts/audit_axioms.py`, `references/*.md`(3編) |
| [`rocq-ltac-best-practice`](skills/rocq-ltac-best-practice)         | トップダウン証明法、破壊的インバージョンマクロ(`inv`)、契約不変性(ヘッダーフェンス)、タクティック自動化階層  | `scripts/lint_proof_contract.py`, `references/*.md`(7編)                                                  |

## 導入方法

[Releases](https://github.com/MI-1222/rocq-ltac-skills/releases) から最新の `rocq-ltac-skills.zip` をダウンロードし、お使いのエージェント環境やプロジェクトの `skills/` ディレクトリに展開してください。

各スキルディレクトリ(`skills/<skill-name>/`)には、エージェント用指示書(`SKILL.md`)が含まれています。

## ディレクトリ構成

```text
skills/
├── rocq-ltac-interactive-proof/  # 対話的ゴール取得・REPL連携
├── rocq-ltac-proof-repair/       # エラー診断・修復処方箋
├── rocq-ltac-syntax/             # 構文チェック・方言混同防止
├── rocq-ltac-cli/                # ビルド管理・ログ解析・公理監査
└── rocq-ltac-best-practice/      # 証明プラクティス・契約不変性
```

## ライセンス

[MIT License](LICENSE)
