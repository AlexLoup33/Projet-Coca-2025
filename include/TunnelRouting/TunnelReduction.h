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

#endif