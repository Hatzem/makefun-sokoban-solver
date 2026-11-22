# Sokoban Solver

[![make.fun](https://make.fun/badge/sokoban-solver-01-run-20261121.svg)](https://make.fun)
[![rank](https://make.fun/badge/sokoban-solver-01-run-20261121/Hatzem/makefun-sokoban-solver/rank.svg)](https://make.fun)
[![reward](https://make.fun/badge/sokoban-solver-01-run-20261121/Hatzem/makefun-sokoban-solver/reward.svg)](https://make.fun)

A push-optimal Sokoban solver, built for [make.fun](https://make.fun)'s
"Build the best Sokoban solver, 21 November 2026" bounty.

Each level is a one-square hallway with one to four rooms off it, and a box
that leaves its room can never come back — so the solver splits the level
into rooms and solves each one on its own with a push-optimal A* (dead-square
and freeze-deadlock pruning, min-cost-assignment heuristic), then joins the
room solutions by walking the player through the hallway.
