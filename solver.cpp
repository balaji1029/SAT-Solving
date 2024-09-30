#ifndef SOLVER_H
#define SOLVER_H

#include <iostream>
#include <vector>
#include <utility>
#include "assignments.h"
#include "clause.h"

enum ClauseStatus {
    SATISFIED,
    UNIT,
    UNSATISFIED,
    UNRESOLVED
};

enum UnitPropagationStatus {
    UNIT_CONFLICT,
    UNIT_UNRESOLVED
};

class Solver {

    public:
        Solver() {};

        // Check the status of a clause
        ClauseStatus checkClauseStatus(Clause clause, Assignments assignments) {
            std::vector<int> values;
            int zero_count = 0;
            for (Literal literal : clause) {
                if (assignments.find(literal.getVariable()) != assignments.end()) {
                    bool value = (literal.isNegated()) ? !assignments.at(literal.getVariable()).getValue() : (assignments.at(literal.getVariable())).getValue();
                    values.push_back(value);
                    zero_count += (value == 0);
                } else {
                    values.push_back(-1);
                }
            }

            // for (int value : values) {
            //     std::cout << value << " ";
            // }
            // std::cout << "Zero count: " << zero_count << std::endl;

            if (find(values.begin(), values.end(), true) != values.end()) {
                // std::cout << "SATISFIED" << std::endl;
                return SATISFIED;
            } else if (zero_count == values.size()){
                // std::cout << "UNSATISFIED" << std::endl;
                return UNSATISFIED;
            } else if (zero_count == values.size() - 1) {
                // std::cout << "UNIT" << std::endl;
                return UNIT;
            } else {
                // std::cout << "UNRESOLVED" << std::endl;
                return UNRESOLVED;
            }
        }

        // Unit propagate
        std::pair<UnitPropagationStatus, Clause> unitPropagate(Assignments assignments, Formula formula) {
            std::vector<Clause> clauses = formula.getClauses();
            bool finish = false;
            while (!finish) {
                finish = true;
                for (Clause clause : clauses) {
                    ClauseStatus status = checkClauseStatus(clause, assignments);
                    // std::cout << "Clause status: " << (int) status << std::endl;
                    // std::cout << "Clause: " << clause << std::endl;
                    if (status == UNRESOLVED || status == SATISFIED) {
                        continue;
                    } else if (status == UNIT) {
                        // std::cout << "Found unit clause: " << clause << std::endl;
                        for (Literal literal : clause) {
                            if (assignments.find(literal.getVariable()) == assignments.end()) {
                                assignments.assign(literal.getVariable(), !literal.isNegated(), clause);
                                std::cout << "Assigning " << literal.getVariable() << " = " << !literal.isNegated() << std::endl;
                                break;
                            }
                        }
                        finish = false;
                    } else {
                        return {UNIT_CONFLICT, clause};
                    }
                }
            }
            return {UNIT_UNRESOLVED, Clause()};
        }

        // Add a clause to the formula
        void addClause(Formula& formula, Clause clause) {
            formula.addClause(clause);
        }

        // Check if all variables are assigned
        bool allAssigned(Formula formula, Assignments assignments) {
            for (int variable : formula.getVariables()) {
                if (assignments.find(variable) == assignments.end()) {
                    return false;
                }
            }
            return true;
        }

        // Pick a variable to assign
        std::pair<int, bool> pickVariable(Formula formula, Assignments assignments) {
            for (int variable : formula.getVariables()) {
                if (assignments.find(variable) == assignments.end()) {
                    return {variable, true};
                }
            }
            return {-1, false};
        }

        // Backtrack
        void backtrack(Assignments& assignments, int level) {
            std::vector<int> to_remove;
            for (auto it = assignments.begin(); it != assignments.end(); it++) {
                if (it->second.getDecisionLevel() > level) {
                    to_remove.push_back(it->first);
                }
            }
            for (int variable : to_remove) {
                assignments.unassign(variable);
                std::cout << "Unassigning " << variable << std::endl;
            }
        }

        // Solve the formula
        Assignments CDCLSolve(Formula formula) {
            Assignments assignments = Assignments();
            int level = 0;
            
            std::pair<UnitPropagationStatus, Clause> unit_propagation = unitPropagate(assignments, formula);
            // std::cout << "Unit propagation: " << unit_propagation.first << std::endl;
            if (unit_propagation.first == UNIT_CONFLICT) {
                return assignments;
            }
            // std::cout << "Unit propagation: " << unit_propagation.first << std::endl;

            while (!allAssigned(formula, assignments)) {
                std::pair<int, bool> variable = pickVariable(formula, assignments);
                assignments.increaseDecisionLevel();
                assignments.assign(variable.first, variable.second, Clause());
                std::cout << "Decision: " << variable.first << " = " << variable.second << std::endl;
                while (true) {
                    for (Clause clause : formula.getClauses()) {
                        std::cout << "Clause: " << clause << std::endl;
                    }
                    unit_propagation = unitPropagate(assignments, formula);
                    if (unit_propagation.first != UNIT_CONFLICT) {
                        break;
                    }
                    addClause(formula, unit_propagation.second);
                    std::cout << "Adding clause: " << unit_propagation.second << std::endl;
                    std::cout << "Clause size: " << formula.length() << std::endl;
                    backtrack(assignments, level);
                    assignments.setDecisionLevel(level);
                }
            }

            return assignments;
        }

        Clause resolve(Clause clause1, Clause clause2, int variable) {
            std::set<Literal> result;
            for (Literal literal : clause1) {
                result.insert(literal);
            }
            for (Literal literal : clause2) {
                result.insert(literal);
            }
            result.erase(Literal(variable, true));
            result.erase(Literal(variable, false));
            return Clause(std::vector<Literal>(result.begin(), result.end()));
        }

        std::pair<int, Clause> conflict_analysis(Clause clause, Assignments assignments) {
            if (assignments.getDecisionLevel() == 0) {
                return {-1, Clause()};
            }

            std::vector<Literal> literals;
            for (Literal literal : clause) {
                if (assignments.find(literal.getVariable()) != assignments.end() && assignments.at(literal.getVariable()).getDecisionLevel() == assignments.getDecisionLevel()) {
                    literals.push_back(literal);
                }
            }

            while (literals.size() != 1) {
                literals.erase(
                    std::remove_if(literals.begin(), literals.end(), [&](const Literal& lit) {
                        return assignments[lit.getVariable()].getAntecedent() == Clause();
                    }),
                    literals.end()
                );

                Literal literal = literals.back();
                Clause antecedant = assignments[literal.getVariable()].getAntecedent();
                Clause clause = resolve(clause, antecedant, literal.getVariable());

                literals = std::vector<Literal>();
                for (Literal literal : clause) {
                    if (assignments.find(literal.getVariable()) != assignments.end() && assignments.at(literal.getVariable()).getDecisionLevel() == assignments.getDecisionLevel()) {
                        literals.push_back(literal);
                    }
                }
            }

            std::set<int> decision_levels;
            for (Literal literal : clause) {
                decision_levels.insert(assignments[literal.getVariable()].getDecisionLevel());
            }
            std::vector<int> decision_levels_vector(decision_levels.begin(), decision_levels.end());
            std::sort(decision_levels_vector.begin(), decision_levels_vector.end());

            if (decision_levels_vector.size() <= 1) {
                return {0, clause};
            } else {
                return {decision_levels_vector[decision_levels_vector.size()-2], clause};
            }
        }
};

#endif