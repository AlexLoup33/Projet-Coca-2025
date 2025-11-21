/**
 * @file TunnelReduction.h
 * @author Vincent Penelle (vincent.penelle@u-bordeaux.fr)
 * @brief An implementation of the reduction of the Tunnel Routing problem to SAT. Converts a network n and a bound b to a propositional formula that is satisfiable if and only there is a well-formed simple path of size b from the source to the target. A satisfying valuation represents such a path.
 * Provides functions to generate the formula, the necessary variables, and decoding a path from a valuation.
 * @version 0.1
 * @date 2025-10-03
 *
 * @copyright Creative Commons
 *
 */

#ifndef TUNNEL_RED_H
#define TUNNEL_RED_H

#include "TunnelNetwork.h"
#include <z3.h>

/**
 * @brief Generates a propositional formula satisfiable if and only if there is a well-formed simple path of size @p bound from the initial node of @p network to its final node.
 *
 * @param ctx The solver context.
 * @param network A Tunnel Network.
 * @param length The size of the target path.
 * @return Z3_ast The formula
 * @pre @p network must be initialized.
 */
Z3_ast tn_reduction(Z3_context ctx, const TunnelNetwork network, int length);

/**
 * @brief Gets the well-formed path from the model @p model.
 *
 * @param ctx The solver context.
 * @param model A variable assignment.
 * @param network A Tunnel Network.
 * @param bound The size of the path.
 * @param path The path
 * @pre @p path must be an array of size @p bound+1.
 */
void tn_get_path_from_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound, tn_step *path);

/**
 * @brief Prints (in pretty format) which variables used by the tunnel reduction are true in @p model.
 *
 * @param ctx The solver context.
 * @param model A variable assignment.
 * @param network A tunnel network.
 * @param bound The size of the path.
 */
void tn_print_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound);


/**
 * @brief φ1 : Existence, single operation, and single height.
 * 
 * @param ctx The solver context.
 * @param network The graph
 * @param length The length of the sought path.
 * @return Z3_ast
 */
Z3_ast tn_exist_uniqueOp_uniqueHeight(Z3_context ctx, const TunnelNetwork network, int length);


/**
 * @brief φ2 : Initial and final stack
 * 
 * @param ctx The solver context.
 * @param network The graph
 * @param length The length of the sought path.
 * @return Z3_ast
 */
Z3_ast tn_init_final_stack(Z3_context ctx, const TunnelNetwork network, int length);


/**
 * @brief φ3 : Stack height transition rule for Transmission
 * 
 * @param length The length of the sought path.
 * @param pos The current position of the path.
 * @return Z3_ast
 */
Z3_ast tn_transition_stack_height(Z3_context ctx, TunnelNetwork network, int length, int pos);

/**
 * @brief φ4 : Stack height transition rule for Encapsulation
 * 
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast
 */
Z3_ast tn_encapsulation_stack_height(Z3_context ctx, TunnelNetwork network, int length, int pos);

/**
 * @brief φ5 : Stack height transition rule for Decapsulation
 * 
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast
 */
Z3_ast tn_decapsulation_stack_height(Z3_context ctx, TunnelNetwork network, int length, int pos);

/**
 * @brief φ6 : Stack content coherence (exactly with one protocol (4 or 6))
 * 
 * @param ctx The solver context.
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast 
 */
Z3_ast tn_stack_content_coherence(Z3_context ctx, int length, int pos);

/**
 * @brief φ7 :  Conditions necessary for an operation to be feasible
 * 
 * @param ctx The solver context.
 * @param network The graph.
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast 
 */
Z3_ast tn_operation_feasibility(Z3_context ctx, TunnelNetwork network, int length, int pos);

/**
 * @brief φ8  φ9  φ10 : Stack preservation logic for Transmission, Encapsulation, and Decapsulation
 * 
 * @param ctx The solver context.
 * @param network The graph
 * @param length The length of the sought path.
 * @return Z3_ast
 */
Z3_ast tn_stack_preservation_logic(Z3_context ctx, const TunnelNetwork network, int length);

/**
 * @brief φ11 : Verification of constraints on transitions
 * 
 * @details if we are at (u, pos, h), then at pos+1 we must be in a successor of u
 * @param ctx The solver context.
 * @param network The graph
 * @param length The length of the sought path.
 * @return Z3_ast
 */

Z3_ast tn_edge_constraints(Z3_context ctx, const TunnelNetwork network, int length);

#endif