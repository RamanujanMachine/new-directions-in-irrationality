LINEAR INDEPENDENCE OF 1, zeta(2), L(2,chi_{-3}) FROM ONE CMF TRAJECTORY
22 October 2026. Supplement to "New Directions in Irrationality", arXiv:2610.27799;
an explicit Apery-style proof of the theorem of Calegari, Dimitrov and Tang,
arXiv:2408.15403. To be included in the next arXiv version of the paper.

Open calegari_cmf_positive_delta.ipynb. The notebook embeds the endpoint
evaluator, analytic checks and complete standalone arithmetic verifier.
Install requirements.txt; the RamanujanTools Git commit is pinned.

WHAT THE NEW ANALYTIC SECTION ADDS
1. An explicit positive four-variable beta integral for the actual MG state.
2. An elementary bound on all three components with exponential base
   eta = 228249336488800000/1978419655660313589123979
       = 1.15369525285382354677...e-7.
3. Exact separation from the other two modes, which have modulus
   5.1264502899968973...e13. Hence the state is recessive.
4. Exact initial-state evaluation with
   D G_0^T=3888, X G_0^T=3888 C, Y G_0^T=3888 zeta(2).
5. Dual convergence identifying both limits and deriving their error rate.

CONCLUSION AND SCOPE
The limit and error-rate assumptions of the earlier notebook are discharged.
Combining the analytic argument with the written arithmetic valuation lemmas
and their finite certificate gives, for every fixed integer (A,B)!=(0,0),

    liminf delta_N(A,B) > 0.00010.

Here alpha(A,B)=A(C+2*zeta(2)/3)+B(C-2*zeta(2)/3), C=L(2,chi_-3).
The resulting irrationality of every such mixture implies that 1,C,zeta(2)
are linearly independent over Q.

E = 64.476159691897769244147439665711...
H <= 64.469498127103114075274153758067...
Certified lower comparison = 0.000103328938306945387419974368047...

The Python checks verify finite rational algebra and interval comparisons.
The analytic and general prime-valuation steps are written mathematical
arguments, not a proof-assistant formalization. Barnes quadrature is only
an independent regression; it is not a premise of the proof.

FILES
- calegari_cmf_positive_delta.ipynb: complete executed notebook.
- PROOF.txt: combined analytic and arithmetic description.
- ANALYTIC_PROOF.txt: the new integral, initial-state and recessiveness argument.
- analytic_limit_certificate.py and analytic_limit_result.json: exact checks.
- ARITHMETIC_ARGUMENT.txt: preserved original arithmetic argument and input contract.
- positive_delta_certificate.py: unchanged standalone arithmetic verifier.
- notebook_outputs/: exact matrices, 60 approximants, analytic result, chamber
  checkpoint, arithmetic result, and combined summary.
- prior_fresh_notebook_execution.log: earlier full 1,158-chamber computation.
- verification.json and manifest.json: execution and file-integrity records.

REPRODUCTION
Run all notebook cells, or:

    python run_notebook.py calegari_cmf_positive_delta.ipynb

A clean directory reconstructs the matrices. REBUILD_CMFS=True forces that
reconstruction even if a cache is present. FRESH_ARITHMETIC=False reuses the
source-hashed checkpoint included here; True recomputes all 1,158 chambers.
The latest run rechecks the analytic part and resumes that arithmetic checkpoint.
The original fresh arithmetic run is preserved separately.

Standalone commands:

    python analytic_limit_certificate.py --quadrature
    python positive_delta_certificate.py --fresh

The original standalone arithmetic verifier still states its analytic input
contract. It has not been silently altered: Sections 6 and 6A of the notebook
now prove those prerequisites.

FINITE-DEPTH VALUES
At N=640: delta(C)=+0.00013945 and delta(C-2*zeta(2)/3)=+0.04922833.
Generic mixtures are not yet asymptotic at these depths and several are
still negative. Finite-depth values are not used in the proof.

EXECUTION RESULT
All 15 code cells executed successfully through IPython, with zero error outputs.
Elapsed notebook execution: 98.81 seconds.
The analytic checks passed, including exact initial pairings, beta exponents,
root separation, and independent Barnes regression at 50 and 80 digits.
The 1,158 arithmetic chambers were loaded from the source-hashed checkpoint;
the prior fresh calculation remains in prior_fresh_notebook_execution.log.
The exact matrix cache matched the previously reconstructed matrices.
See verification.json for the execution mode and integrity records.
For console reproduction: python run_notebook.py calegari_cmf_positive_delta.ipynb
