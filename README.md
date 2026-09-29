> ⚠️ **WORK IN PROGRESS / DRAFT** 
> This repository contains my personal research artifact notes, Lean 4 formalization code, and draft companion paper.

# Formalization of Combinatorial Algebraic Geometry in Lean 4

This repository contains the machine-checked Lean 4 formalization and research write-up for Section 3 of Matviichuk (2023), focusing on log symplectic biresidue matrices, smoothable edge cycles, and spectral graph properties.

## 👥 Project Context & Role
- **Department:** Department of Mathematics, The Chinese University of Hong Kong (CUHK)
- **Principal Investigator:** Prof. Mykola Matviichuk
- ****
- **My Role:** Formalized Section 3 (Lemma 3.2, Family Y and Z, Theorem C on case family Y,Z), set up Mathlib graph structures, and implemented case analysis for Theorem C cycle classifications.

## 📄 Research Documentation & Artifacts
- [📄 Read Companion Research Write-up (PDF)](Lean_Project_draft_1.pdf) *(Draft in progress)*

## 🛠️ Machine-Checked Results in Lean 4
- **Biresidue Structures & Graphs:** Modeled skew-symmetric biresidue matrices using Mathlib, formalizing Lemma 3.1 (degree bounds on smoothable subgraphs).
- **Classification of Smoothable Cycles:** Verified full case analysis for Theorem C across families ($C_{n,k}, C_{n,k,I}, Y_n, Z_n$).
- **Spectral Properties:** Formalized roots-of-unity eigenvector expansions for exact rank formulas (Lemma 3.3) and corank-1 realizability (Corollary 3.4).

## 💻 Build Instructions
Make sure you have [Lean 4 & Lake](https://leanprover-community.github.io/get_started.html) installed:

```bash
# Fetch pre-compiled Mathlib dependencies
lake exe cache get

# Build and verify all formal proofs
lake build
