#ifndef ASSIGNMENTS_H
#define ASSIGNMENTS_H

#include <iostream>
#include <unordered_map>
#include "literal.h"
#include "assignment.h"
#include "clause.h"
#include "formula.h"


class Assignments : public std::unordered_map<int, Assignment> {

    private:

    int decision_level;

    public:

    Assignments() : std::unordered_map<int, Assignment>(), decision_level(0) {}

    // Get the decision level
    bool value(Literal literal) {
        if (find(literal.getVariable()) == end()) {
            return false;
        }
        if (literal.isNegated()) {
            return !at(literal.getVariable()).getValue();
        } else {
            return at(literal.getVariable()).getValue();
        }
    }

    // Assign a value to a variable
    void assign(int variable, bool value, Clause antecedent) {
        this->operator[](variable) = Assignment(value, antecedent, decision_level);
    }

    // Unassign a variable
    void unassign(int variable) {
        erase(variable);
    }

    // Increase the decision level
    void increaseDecisionLevel() {
        decision_level++;
    }

    int getDecisionLevel() {
        return decision_level;
    }

    void setDecisionLevel(int level) {
        decision_level = level;
    }

    // Check whether the assignments actually satisfies the formula
    bool satisfy(Formula formula) {
        for (Clause clause : formula) {
            bool clause_satisfied = false;
            for (Literal literal : clause) {
                if (value(literal)) {
                    clause_satisfied = true;
                    break;
                }
            }
            if (!clause_satisfied) {
                return false;
            }
        }
        return true;
    }
};

#endif