#include "TunnelReduction.h"
#include "Z3Tools.h"
#include "stdio.h"
#include <stdlib.h>

// --- Variables ---

/**
 * @brief Creates the variable "x_{node,pos,stack_height}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param node A node.
 * @param pos The path position.
 * @param stack_height The highest cell occupied of the stack at that position.
 * @return Z3_ast
 */
Z3_ast tn_path_variable(Z3_context ctx, int node, int pos, int stack_height)
{
    char name[60];
    snprintf(name, 60, "node %d,pos %d, height %d", node, pos, stack_height);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Creates the variable "y_{pos,height,4}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param pos The path position.
 * @param height The height of the cell described.
 * @return Z3_ast
 */
Z3_ast tn_4_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "4 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Creates the variable "y_{pos,height,6}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param pos The path position.
 * @param height The height of the cell described.
 * @return Z3_ast
 */
Z3_ast tn_6_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "6 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Wrapper to have the correct size of the array representing the stack (correct cells of the stack will be from 0 to (get_stack_size(length)-1)).
 *
 * @param length The length of the sought path.
 * @return int
 */
int get_stack_size(int length)
{
    return length / 2 + 1;
}

/**
 * @brief Checks if ANY node is active at (pos, height)
 *
 * @param ctx The solver context.
 * @param num_nodes The number of nodes.
 * @param height The height of the cell described.
 * @return Z3_ast
 */
Z3_ast tn_any_node_at(Z3_context ctx, int num_nodes, int pos, int height) {
    Z3_ast *nodes = malloc(num_nodes * sizeof(Z3_ast));
    for(int i=0; i<num_nodes; i++) {
        nodes[i] = tn_path_variable(ctx, i, pos, height);
    }
    Z3_ast res = Z3_mk_or(ctx, num_nodes, nodes);
    free(nodes);
    return res;
}

// --- SAT Formulas ---

/**
 * @brief φ1 : Existence, single operation, and single height.
 * 
 * @param ctx The solver context.
 * @param network The graph
 * @param length The length of the sought path.
 * @return Z3_ast
 */
Z3_ast tn_exist_uniqueOp_uniqueHeight(Z3_context ctx, const TunnelNetwork network, int length)
{
    int stack_size = get_stack_size(length);
    int num_nodes = tn_get_num_nodes(network);
    int num_vars = stack_size * num_nodes;
    int num_positions = length + 1; 

    Z3_ast *pos_constraints = malloc(num_positions * sizeof(Z3_ast));

    for (int i = 0; i <= length; i++) {
        Z3_ast *vars = malloc(num_vars * sizeof(Z3_ast));
        int idx = 0;
        for (int h = 0; h < stack_size; h++) {
            for (int op = 0; op < num_nodes; op++) {
                vars[idx++] = tn_path_variable(ctx, op, i, h);
            }
        }

        Z3_ast existence = Z3_mk_or(ctx, num_vars, vars);
        
        int num_pairs = num_vars * (num_vars - 1) / 2;
        Z3_ast *clauses = malloc(num_pairs * sizeof(Z3_ast));
        int c = 0;
        for (int p = 0; p < num_vars; p++) {
            for (int q = p + 1; q < num_vars; q++) {
                Z3_ast not_both[2] = { Z3_mk_not(ctx, vars[p]), Z3_mk_not(ctx, vars[q]) };
                clauses[c++] = Z3_mk_or(ctx, 2, not_both);
            }
        }
        Z3_ast uniq = Z3_mk_and(ctx, num_pairs, clauses);

        pos_constraints[i] = Z3_mk_and(ctx, 2, (Z3_ast[]){existence, uniq});

        free(vars);
        free(clauses);
    }

    Z3_ast result = Z3_mk_and(ctx, num_positions, pos_constraints);
    free(pos_constraints);
    return result;
}

/**
 * @brief φ2 : Initial and final stack
 * 
 * @param ctx The solver context.
 * @param network The graph
 * @param length The length of the sought path.
 * @return Z3_ast
 */
Z3_ast tn_init_final_stack(Z3_context ctx, const TunnelNetwork network, int length)
{
    int init  = tn_get_initial(network);
    int final = tn_get_final(network);

    Z3_ast init_state = Z3_mk_and(ctx, 2, (Z3_ast[]){
        tn_path_variable(ctx, init, 0, 0),
        tn_4_variable(ctx, 0, 0)
    });

    Z3_ast final_state = Z3_mk_and(ctx, 2, (Z3_ast[]){
        tn_path_variable(ctx, final, length, 0),
        tn_4_variable(ctx, length, 0)
    });

    return Z3_mk_and(ctx, 2, (Z3_ast[]){ init_state, final_state });
}

/**
 * @brief φ3 : Stack height transition rule for Transmission
 * 
 * @param ctx The solver context.
 * @param length The length of the sought path.
 * @param pos The current position of the path.
 * @return Z3_ast
 */
Z3_ast tn_transition_stack_height(Z3_context ctx, TunnelNetwork network, int length, int pos)
{
    int stack_size = get_stack_size(length);
    int num_nodes = tn_get_num_nodes(network);
    // We will generate one constraint per (u, h)
    Z3_ast *constraints = malloc(num_nodes * stack_size * sizeof(Z3_ast));
    int count = 0;

    //is there ANY node at height h at step pos+1? If true, height h is preserved → potential Transmission transition.
    Z3_ast next_any_h[stack_size];
    for(int h=0; h<stack_size; h++) next_any_h[h] = tn_any_node_at(ctx, num_nodes, pos+1, h);

    //for each height h and each node u
    for (int h = 0; h < stack_size; h++) {
        for (int u = 0; u < num_nodes; u++) {
            // We are at node u at step pos with height h AND at step pos+1 there is some node at the SAME height h
            // height is preserved → Transmission
            Z3_ast premise = Z3_mk_and(ctx, 2, (Z3_ast[]){
                tn_path_variable(ctx, u, pos, h),
                next_any_h[h] 
            });

            // Stack content at (pos, h)
            Z3_ast y4 = tn_4_variable(ctx, pos, h);
            Z3_ast y6 = tn_6_variable(ctx, pos, h);
            
            // Check whether node u allows the required transmission type.
            Z3_ast can_t4 = tn_node_has_action(network, u, transmit_4) ? Z3_mk_true(ctx) : Z3_mk_false(ctx);
            Z3_ast can_t6 = tn_node_has_action(network, u, transmit_6) ? Z3_mk_true(ctx) : Z3_mk_false(ctx);

            //If the content is 4, node u must allow transmit_4.
            Z3_ast valid_4 = Z3_mk_implies(ctx, y4, can_t4);
            //If the content is 6, node u must allow transmit_6.
            Z3_ast valid_6 = Z3_mk_implies(ctx, y6, can_t6);

            // Both conditions must hold (for 4 and for 6)
            Z3_ast conclusion = Z3_mk_and(ctx, 2, (Z3_ast[]){valid_4, valid_6});
            constraints[count++] = Z3_mk_implies(ctx, premise, conclusion);
        }
    }
    Z3_ast res = Z3_mk_and(ctx, count, constraints);
    free(constraints);
    return res;
}

/**
 * @brief φ4 : Stack height transition rule for Encapsulation
 *
 * @param ctx The solver context.
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast
 */
Z3_ast tn_encapsulation_stack_height(Z3_context ctx, TunnelNetwork network, int length, int pos){
    int stack_size = get_stack_size(length);
    if (stack_size <= 1) return Z3_mk_true(ctx);
    int num_nodes = tn_get_num_nodes(network);
    // We will generate one constraint per (u, h)
    Z3_ast *constraints = malloc(num_nodes * (stack_size-1) * sizeof(Z3_ast));
    int count = 0;

    // Is there ANY node at height h+1 at step pos+1 ? Can the stack increase by one level?
    Z3_ast next_any_h_plus[stack_size];
    for(int h=0; h<stack_size-1; h++) next_any_h_plus[h] = tn_any_node_at(ctx, num_nodes, pos+1, h+1);

    //for each height h (except the top one) and each node u
    for (int h = 0; h < stack_size - 1; h++) {
        for(int u=0; u < num_nodes; u++) {
            // Premise: We are at u at h, and in the next step we are at h+1 (Push)
            Z3_ast premise = Z3_mk_and(ctx, 2, (Z3_ast[]){
                tn_path_variable(ctx, u, pos, h),
                next_any_h_plus[h]
            });

            // Stack content before the PUSH (h, pos)
            Z3_ast y4_curr = tn_4_variable(ctx, pos, h);
            Z3_ast y6_curr = tn_6_variable(ctx, pos, h);
            // Stack content after the PUSH (h+1, pos+1)
            Z3_ast y4_next = tn_4_variable(ctx, pos+1, h+1);
            Z3_ast y6_next = tn_6_variable(ctx, pos+1, h+1);

            // PUSH 4 → 4
            Z3_ast c1 = Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, (Z3_ast[]){y4_curr, y4_next}), 
                        tn_node_has_action(network, u, push_4_4) ? Z3_mk_true(ctx) : Z3_mk_false(ctx));
            
            // PUSH 4 → 6
            Z3_ast c2 = Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, (Z3_ast[]){y4_curr, y6_next}), 
                        tn_node_has_action(network, u, push_4_6) ? Z3_mk_true(ctx) : Z3_mk_false(ctx));
            // PUSH 6 → 4
            Z3_ast c3 = Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, (Z3_ast[]){y6_curr, y4_next}), 
                        tn_node_has_action(network, u, push_6_4) ? Z3_mk_true(ctx) : Z3_mk_false(ctx));
            // PUSH 6 → 6
            Z3_ast c4 = Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, (Z3_ast[]){y6_curr, y6_next}), 
                        tn_node_has_action(network, u, push_6_6) ? Z3_mk_true(ctx) : Z3_mk_false(ctx));

            constraints[count++] = Z3_mk_implies(ctx, premise, Z3_mk_and(ctx, 4, (Z3_ast[]){c1, c2, c3, c4}));
        }
    }
    Z3_ast res = Z3_mk_and(ctx, count, constraints);
    free(constraints);
    return res;
}

/**
 * @brief φ5 : Stack height transition rule for Decapsulation
 * 
 * @param ctx The solver context.
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast
 */
Z3_ast tn_decapsulation_stack_height(Z3_context ctx, TunnelNetwork network, int length, int pos){
    int stack_size = get_stack_size(length);
    if (stack_size <= 1) return Z3_mk_true(ctx);
    int num_nodes = tn_get_num_nodes(network);

    Z3_ast *constraints = malloc(num_nodes * (stack_size-1) * sizeof(Z3_ast));
    int count = 0;

    Z3_ast next_any_h_minus[stack_size];
    for(int h=1; h<stack_size; h++) next_any_h_minus[h] = tn_any_node_at(ctx, num_nodes, pos+1, h-1);

    for (int h = 1; h < stack_size; h++) {
        for(int u=0; u < num_nodes; u++) {
            //Condition : We are at u at h, and in the next step we are at h-1 (Pop)
            Z3_ast premise = Z3_mk_and(ctx, 2, (Z3_ast[]){
                tn_path_variable(ctx, u, pos, h),
                next_any_h_minus[h]
            });

            Z3_ast y4_top = tn_4_variable(ctx, pos, h); 
            Z3_ast y6_top = tn_6_variable(ctx, pos, h);
            Z3_ast y4_under = tn_4_variable(ctx, pos, h-1);
            Z3_ast y6_under = tn_6_variable(ctx, pos, h-1);
            
            // Cas 1: Top 4, Under 4 (44↓4) -> pop_4_4
            Z3_ast c1 = Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, (Z3_ast[]){y4_top, y4_under}), 
                        tn_node_has_action(network, u, pop_4_4) ? Z3_mk_true(ctx) : Z3_mk_false(ctx));
            
            // Cas 2: Top 4, Under 6 (64↓6) -> It's pop_6_4 (you remove 4 to reveal 6)
            Z3_ast c2 = Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, (Z3_ast[]){y4_top, y6_under}), 
                        tn_node_has_action(network, u, pop_6_4) ? Z3_mk_true(ctx) : Z3_mk_false(ctx));
            
            // Cas 3: Top 6, Under 4 (46↓4) -> It's pop_4_6 (remove 6 to reveal 4)
            Z3_ast c3 = Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, (Z3_ast[]){y6_top, y4_under}), 
                        tn_node_has_action(network, u, pop_4_6) ? Z3_mk_true(ctx) : Z3_mk_false(ctx));
            
            // Cas 4: Top 6, Under 6 (66↓6) -> pop_6_6
            Z3_ast c4 = Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, (Z3_ast[]){y6_top, y6_under}), 
                        tn_node_has_action(network, u, pop_6_6) ? Z3_mk_true(ctx) : Z3_mk_false(ctx));

            constraints[count++] = Z3_mk_implies(ctx, premise, Z3_mk_and(ctx, 4, (Z3_ast[]){c1, c2, c3, c4}));
        }
    }
    Z3_ast res = Z3_mk_and(ctx, count, constraints);
    free(constraints);
    return res;
}

/**
 * @brief φ6 : Stack content coherence (exactly with one protocol (4 or 6))
 * 
 * @param ctx The solver context.
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast 
 */
Z3_ast tn_stack_content_coherence(Z3_context ctx, int length, int pos){
    int stack_size = get_stack_size(length);
    Z3_ast *constraints = malloc(stack_size * sizeof(Z3_ast));

    for (int h = 0; h < stack_size; h++) {
        Z3_ast y4 = tn_4_variable(ctx, pos, h);
        Z3_ast y6 = tn_6_variable(ctx, pos, h);
        constraints[h] = Z3_mk_xor(ctx, y4, y6);
    }
    Z3_ast result = Z3_mk_and(ctx, stack_size, constraints);
    free(constraints);
    return result;
}

/**
 * @brief φ7 :  Conditions necessary for an operation to be feasible
 * 
 * @param ctx The solver context.
 * @param network The graph.
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast 
 */
Z3_ast tn_operation_feasibility(Z3_context ctx, TunnelNetwork network, int length, int pos){
    int stack_size = get_stack_size(length);
    int num_nodes = tn_get_num_nodes(network);
    // (num_nodes * stack_size * 2) because each node/height may generate 1 or 2 constraints.
    Z3_ast *constraints = malloc(num_nodes * stack_size * sizeof(Z3_ast));
    int count = 0;

    for(int h=0; h<stack_size; h++) {
        for(int u=0; u<num_nodes; u++) {
            // x_{u,pos,h} : node u is active at position pos and height h
            Z3_ast active = tn_path_variable(ctx, u, pos, h);
            // y_{pos,h,4} and y_{pos,h,6}: the top of the stack is respectively 4 or 6
            Z3_ast y4 = tn_4_variable(ctx, pos, h);
            Z3_ast y6 = tn_6_variable(ctx, pos, h);

            //operations can only be executed if the top-of-stack is 4.
            bool can_input_4 = tn_node_has_action(network, u, transmit_4) ||
                               tn_node_has_action(network, u, push_4_4) ||
                               tn_node_has_action(network, u, push_4_6) ||
                               tn_node_has_action(network, u, pop_4_4) ||
                               tn_node_has_action(network, u, pop_6_4); // pop_6_4 signifie Top=4, Under=6

            //These operations can only be executed if the top-of-stack is 6.                  
            bool can_input_6 = tn_node_has_action(network, u, transmit_6) ||
                               tn_node_has_action(network, u, push_6_4) ||
                               tn_node_has_action(network, u, push_6_6) ||
                               tn_node_has_action(network, u, pop_4_6) || // pop_4_6 signifie Top=6, Under=4
                               tn_node_has_action(network, u, pop_6_6);
            // If node u cannot use top=4, forbid y4 whenever active is true
            if (!can_input_4) {
                constraints[count++] = Z3_mk_implies(ctx, active, Z3_mk_not(ctx, y4));
            }
            // If node u cannot use top=6, forbid y6 whenever active is true
            if (!can_input_6) {
                constraints[count++] = Z3_mk_implies(ctx, active, Z3_mk_not(ctx, y6));
            }
        }
    }
    Z3_ast res = Z3_mk_and(ctx, count, constraints);
    free(constraints);
    return res;
}

/**
 * @brief Builds a conjunction expressing that the lower part of the stack 
 *        (prefix 0..limit-1) remains identical between positions pos and next_pos.
 *
 * @details This function creates the formula: ( y[pos,k,a] ↔ y[pos+1,k,a] )
 * for both possible contents (4 and 6).
 *
 * @param ctx       The solver context.
 * @param pos       The current position in the path.
 * @param next_pos  The next position (pos+1).
 * @param limit     The number of stack cells to preserve (prefix size).
 * @return Z3_ast 
 */
Z3_ast tn_prefix_equal(Z3_context ctx, int pos, int next_pos, int limit){
    if (limit <= 0) {
        return Z3_mk_true(ctx);
    }

    Z3_ast *eqs = malloc(limit * sizeof(Z3_ast));
    for (int k = 0; k < limit; k++) {
        eqs[k] = Z3_mk_and(ctx, 2, (Z3_ast[]){
            Z3_mk_iff(ctx, tn_4_variable(ctx, pos, k), tn_4_variable(ctx, next_pos, k)),
            Z3_mk_iff(ctx, tn_6_variable(ctx, pos, k), tn_6_variable(ctx, next_pos, k))
        });
    }
    Z3_ast res = Z3_mk_and(ctx, limit, eqs);
    free(eqs);
    return res;
}

/**
 * @brief φ8-Transmission: preservation of stack contents when the height remains the same.
 *
 * @details If the stack height is h at both pos and pos+1, then the lower part of the stack
 * (0..h-1) must stay identical.
 *
 * @param ctx       The solver context.
 * @param num_nodes Number of nodes in the network (used for ∃ over x variables).
 * @param pos       Current position.
 * @param h         Current stack height.
 * @return Z3_ast
 */
static Z3_ast tn_stack_preservation_transmission(Z3_context ctx, int num_nodes, int pos, int h) 
{
    // Condition: stack height = h at pos AND at pos+1
    Z3_ast any_at_h = tn_any_node_at(ctx, num_nodes, pos,   h);
    Z3_ast next_at_h = tn_any_node_at(ctx, num_nodes, pos+1, h);
    Z3_ast trans_cond = Z3_mk_and(ctx, 2, (Z3_ast[]){ any_at_h, next_at_h });

    // Preserve cells 0..h-1
    Z3_ast trans_preserves = tn_prefix_equal(ctx, pos, pos+1, h);

    return Z3_mk_implies(ctx, trans_cond, trans_preserves);
}

/**
 * @brief φ9-Encapsulation: preservation of stack contents when height increases (h → h+1).
 *
 * @details When encapsulating, a new element is pushed on top of the stack. 
 * Therefore stack cells 0..h must remain identical.
 *
 * @param ctx         The solver context.
 * @param num_nodes   Number of graph nodes.
 * @param stack_size  Maximum stack size.
 * @param pos         Current position.
 * @param h           Current stack height.
 * @return Z3_ast
 */
static Z3_ast tn_stack_preservation_encapsulation(Z3_context ctx, int num_nodes, int stack_size, int pos, int h) 
{
    Z3_ast any_at_h = tn_any_node_at(ctx, num_nodes, pos, h);
    // True only if h+1 is a valid height
    Z3_ast next_at_h_plus = Z3_mk_false(ctx);

    if (h + 1 < stack_size) {
        next_at_h_plus = tn_any_node_at(ctx, num_nodes, pos+1, h+1);
    }

    Z3_ast enc_cond = Z3_mk_and(ctx, 2, (Z3_ast[]){ any_at_h, next_at_h_plus });

    // Preserve stack cells 0..h (h+1 cells)
    Z3_ast enc_preserves = tn_prefix_equal(ctx, pos, pos+1, h+1);

    return Z3_mk_implies(ctx, enc_cond, enc_preserves);
}

/**
 * @brief φ10-Decapsulation: preservation of contents when height decreases (h → h-1).
 *
 * @details When popping the top element, the new top becomes cell h-1,
 * therefore the lower cells 0..h-1 must remain identical.
 *
 * @param ctx         The solver context.
 * @param num_nodes   Number of graph nodes.
 * @param pos         Current position.
 * @param h           Current stack height.
 * @return Z3_ast
 */
static Z3_ast tn_stack_preservation_decapsulation(Z3_context ctx, int num_nodes, int pos, int h) 
{
    Z3_ast any_at_h = tn_any_node_at(ctx, num_nodes, pos,   h);
    // True only if h-1 is a valid height
    Z3_ast next_at_h_minus = Z3_mk_false(ctx);

    if (h - 1 >= 0) {
        next_at_h_minus = tn_any_node_at(ctx, num_nodes, pos+1, h-1);
    }

    Z3_ast dec_cond = Z3_mk_and(ctx, 2, (Z3_ast[]){ any_at_h, next_at_h_minus });
    // Preserve cells 0..h-1
    Z3_ast dec_preserves = tn_prefix_equal(ctx, pos, pos+1, h);

    return Z3_mk_implies(ctx, dec_cond, dec_preserves);
}

// --- Global Stack Preservation Feature ---

/**
 * @brief φ8  φ9  φ10 : Stack preservation logic for Transmission, Encapsulation, and Decapsulation
 * 
 * @param ctx The solver context.
 * @param network The graph
 * @param length The length of the sought path.
 * @return Z3_ast
 */
Z3_ast tn_stack_preservation_logic(Z3_context ctx, const TunnelNetwork network, int length){
    int stack_size = get_stack_size(length);
    int num_nodes  = tn_get_num_nodes(network);
    int num_pos    = length;

    Z3_ast *constraints = malloc(num_pos * sizeof(Z3_ast));

    for (int pos = 0; pos < num_pos - 1; pos++) {
        Z3_ast *h_constraints = malloc(stack_size * sizeof(Z3_ast));

        for (int h = 0; h < stack_size; h++) {

            // Combine the 3 possible cases for this height
            Z3_ast c1 = tn_stack_preservation_transmission(
                ctx, num_nodes, pos, h
            );

            Z3_ast c2 = tn_stack_preservation_encapsulation(
                ctx, num_nodes, stack_size, pos, h
            );

            Z3_ast c3 = tn_stack_preservation_decapsulation(
                ctx, num_nodes, pos, h
            );

            h_constraints[h] = Z3_mk_and(ctx, 3, (Z3_ast[]){ c1, c2, c3 });
        }

        constraints[pos] = Z3_mk_and(ctx, stack_size, h_constraints);
        free(h_constraints);
    }

    // Last position does not impose constraints
    constraints[num_pos - 1] = Z3_mk_true(ctx);

    Z3_ast res = Z3_mk_and(ctx, num_pos, constraints);
    free(constraints);
    return res;
}

/**
 * @brief Local edge-transition constraint for a single state (op, pos, h).
 * @details If x_{op,pos,h} is true, then at pos+1 the path must move to some successor
 *          op' of op in the graph, with a valid stack height transition (h-1, h, or h+1).
 *          If no successor is valid for this state, the state is forbidden.
 * @param ctx The solver context.
 * @param network The tunnel network graph.
 * @param length The length of the path being constructed.
 * @param pos The current path position.
 * @param h The current stack height.
 * @param u The current operation (node).
 * @return Z3_ast
 */

static Z3_ast tn_edge_node_constraint(Z3_context ctx, const TunnelNetwork network, int length, int pos, int h, int u){
    int num_nodes  = tn_get_num_nodes(network);
    int stack_size = get_stack_size(length);

    Z3_ast current = tn_path_variable(ctx, u, pos, h);

    Z3_ast *valid_next = malloc(num_nodes * 3 * sizeof(Z3_ast));
    int v_count = 0;

    for (int v = 0; v < num_nodes; v++) {
        if (tn_is_edge(network, u, v)) {
            // Transmission (h)
            valid_next[v_count++] = tn_path_variable(ctx, v, pos + 1, h);

            // Push (h+1)
            if (h + 1 < stack_size) {
                valid_next[v_count++] = tn_path_variable(ctx, v, pos + 1, h + 1);
            }

            // Pop (h-1)
            if (h - 1 >= 0) {
                valid_next[v_count++] = tn_path_variable(ctx, v, pos + 1, h - 1);
            }
        }
    }
    Z3_ast result;
    if (v_count == 0) {
        result = Z3_mk_not(ctx, current);
    } else {
        Z3_ast valid_or = Z3_mk_or(ctx, v_count, valid_next);
        result = Z3_mk_implies(ctx, current, valid_or);
    }

    free(valid_next);
    return result;
}

/**
 * @brief Edge-transition constraint for all operations at a given height.
 * @details Builds the conjunction of all local constraints (op, pos, h)
 *          over every operation op in the graph, enforcing valid transitions for
 *          any active operation at this height.
 * @param ctx The solver context.
 * @param network The tunnel network graph.
 * @param length The length of the path being constructed.
 * @param pos The current path position.
 * @param h The stack height for which constraints are generated.
 * @return Z3_ast
 */

static Z3_ast tn_edge_height_constraint(Z3_context ctx, const TunnelNetwork network, int length, int pos, int h){
    int num_nodes = tn_get_num_nodes(network);
    Z3_ast *node_constraints = malloc(num_nodes * sizeof(Z3_ast));

    for (int u = 0; u < num_nodes; u++) {
        node_constraints[u] = tn_edge_node_constraint(ctx, network, length, pos, h, u);
    }

    Z3_ast res = Z3_mk_and(ctx, num_nodes, node_constraints);
    free(node_constraints);
    return res;
}

/**
 * @brief Edge-transition constraint for all stack heights at a given position.
 * @details Builds the conjunction of all height-level constraints (pos, h)
 *          over every stack height h, ensuring that every possible height at this
 *          position must follow a valid graph transition at pos+1.
 * @param ctx The solver context.
 * @param network The tunnel network graph.
 * @param length The length of the path being constructed.
 * @param pos The current path position.
 * @return Z3_ast
 */

static Z3_ast tn_edge_pos_constraint(Z3_context ctx, const TunnelNetwork network, int length, int pos){
    int stack_size = get_stack_size(length);
    Z3_ast *height_constraints = malloc(stack_size * sizeof(Z3_ast));

    for (int h = 0; h < stack_size; h++) {
        height_constraints[h] = tn_edge_height_constraint(ctx, network, length, pos, h);
    }

    Z3_ast res = Z3_mk_and(ctx, stack_size, height_constraints);
    free(height_constraints);
    return res;
}

/**
 * @brief φ11 : Builds the full edge-transition constraint for the entire path.
 * @details If we are at (op, pos, h), then at pos+1 we must be in a successor of op,
 *          with a stack height compatible with push, pop, or transmission. This function
 *          aggregates all local constraints over every position, height, and operation,
 *          producing the global edge constraint.
 * @param ctx The solver context.
 * @param network The tunnel network graph.
 * @param length The length of the sought path.
 * @return Z3_ast
 */
Z3_ast tn_edge_constraints(Z3_context ctx, const TunnelNetwork network, int length){
    int num_pos = length;
    Z3_ast *pos_constraints = malloc(num_pos * sizeof(Z3_ast));

    for (int pos = 0; pos < num_pos; pos++) {
        pos_constraints[pos] = tn_edge_pos_constraint(ctx, network, length, pos);
    }

    Z3_ast result = Z3_mk_and(ctx, num_pos, pos_constraints);
    free(pos_constraints);
    return result;
}

//------------------------------------------------------------------------------------------------------------------
// --- Main Reduction ---
Z3_ast tn_reduction(Z3_context ctx, const TunnelNetwork network, int length){
    Z3_ast f1 = tn_exist_uniqueOp_uniqueHeight(ctx, network, length);
    Z3_ast f2 = tn_init_final_stack(ctx, network, length);
    
    Z3_ast *f3_parts = malloc(length * sizeof(Z3_ast));
    for (int pos = 0; pos < length; pos++) f3_parts[pos] = tn_transition_stack_height(ctx, network, length, pos);
    Z3_ast f3 = Z3_mk_and(ctx, length, f3_parts);
    free(f3_parts);

    Z3_ast *f4_parts = malloc(length * sizeof(Z3_ast));
    for (int pos = 0; pos < length; pos++) f4_parts[pos] = tn_encapsulation_stack_height(ctx, network, length, pos);
    Z3_ast f4 = Z3_mk_and(ctx, length, f4_parts);
    free(f4_parts);

    Z3_ast *f5_parts = malloc(length * sizeof(Z3_ast));
    for (int pos = 0; pos < length; pos++) f5_parts[pos] = tn_decapsulation_stack_height(ctx, network, length, pos);
    Z3_ast f5 = Z3_mk_and(ctx, length, f5_parts);
    free(f5_parts);

    int num_pos_stack = length + 1;
    Z3_ast *f6_parts = malloc(num_pos_stack * sizeof(Z3_ast));
    for (int pos = 0; pos <= length; pos++) f6_parts[pos] = tn_stack_content_coherence(ctx, length, pos);
    Z3_ast f6 = Z3_mk_and(ctx, num_pos_stack, f6_parts);
    free(f6_parts);

    Z3_ast *f7_parts = malloc(length * sizeof(Z3_ast));
    for (int pos = 0; pos < length; pos++) f7_parts[pos] = tn_operation_feasibility(ctx, network, length, pos);
    Z3_ast f7 = Z3_mk_and(ctx, length, f7_parts);
    free(f7_parts);

    Z3_ast f_preservation = tn_stack_preservation_logic(ctx, network, length);

    Z3_ast f_edges = tn_edge_constraints(ctx, network, length);

    Z3_ast all[9] = { f1, f2, f3, f4, f5, f6, f7, f_preservation, f_edges }; 
    return Z3_mk_and(ctx, 9, all);
}

void tn_get_path_from_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound, tn_step *path)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(bound);
    for (int pos = 0; pos < bound; pos++)
    {
        int src = -1;
        int src_height = -1;
        int tgt = -1;
        int tgt_height = -1;
        for (int n = 0; n < num_nodes; n++)
        {
            for (int height = 0; height < stack_size; height++)
            {
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, n, pos, height)))
                {
                    src = n;
                    src_height = height;
                }
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, n, pos + 1, height)))
                {
                    tgt = n;
                    tgt_height = height;
                }
            }
        }
        int action = 0;
        if (src_height == tgt_height)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
                action = transmit_4;
            else
                action = transmit_6;
        }
        else if (src_height == tgt_height - 1)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
            {
                if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                    action = push_4_4;
                else
                    action = push_4_6;
            }
            else if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                action = push_6_4;
            else
                action = push_6_6;
        }
        else if (src_height == tgt_height + 1)
        {
            {
                if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
                {
                    if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                        action = pop_4_4;
                    else
                        action = pop_6_4;
                }
                else if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                    action = pop_4_6;
                else
                    action = pop_6_6;
            }
        }
        path[pos] = tn_step_create(action, src, tgt);
    }
}

void tn_print_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(bound);
    for (int pos = 0; pos < bound + 1; pos++)
    {
        printf("At pos %d:\nState: ", pos);
        int num_seen = 0;
        for (int node = 0; node < num_nodes; node++)
        {
            for (int height = 0; height < stack_size; height++)
            {
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, node, pos, height)))
                {
                    printf("(%s,%d) ", tn_get_node_name(network, node), height);
                    num_seen++;
                }
            }
        }
        if (num_seen == 0)
            printf("No node at that position !\n");
        else
            printf("\n");
        if (num_seen > 1)
            printf("Several pair node,height!\n");
        printf("Stack: ");
        bool misdefined = false;
        bool above_top = false;
        for (int height = 0; height < stack_size; height++)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, height)))
            {
                if (value_of_var_in_model(ctx, model, tn_6_variable(ctx, pos, height)))
                {
                    printf("|X");
                    misdefined = true;
                }
                else
                {
                    printf("|4");
                    if (above_top)
                        misdefined = true;
                }
            }
            else if (value_of_var_in_model(ctx, model, tn_6_variable(ctx, pos, height)))
            {
                printf("|6");
                if (above_top)
                    misdefined = true;
            }
            else
            {
                printf("| ");
                above_top = true;
            }
        }
        printf("\n");
        if (misdefined)
            printf("Warning: ill-defined stack\n");
    }
    return;
}
