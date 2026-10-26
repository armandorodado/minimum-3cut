# Hard planar instances: light thetas in the dual

Checks for the study of open question 2 of the greedy 3-cut paper: the minimum 3-cut of a
plane graph is min(greedy, minimum light theta in the dual).

| Script | What it checks |
| --- | --- |
| `planar_theta.py trials seed` | OPT = min(greedy, T*), where T* is the cheapest theta in the dual with strands lighter than λ, against brute force; also inside Baker windows. Log: `planar_theta.log` |
| `wheel_theta.py` | The 15-vertex planar wheel-ring instance, where greedy is inexact. Log: `wheel_theta.log` |
| `theta_structure.py trials seed [wmax]` | Structure of optimal light thetas: shortest-path strands, isometric cycles, shortest-path-tree plus few edges. `wmax = 0` gives real weights. Logs: `theta_structure_*.log` |
| `planar_wheels.py` | The planar wheel-ring construction |

Requirements: Python 3.9+, numpy, scipy, networkx. Run from this folder.
