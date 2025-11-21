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
 * @brief vérifie si N'IMPORTE QUEL nœud est actif à (pos, height)
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

// --- Formules ---

/**
 * @brief φ1 : Existence, unique opération et unique hauteur.
 * 
 * @param ctx The solver context.
 * @param network The graph
 * @param length The length of the sought path.
 * @return Z3_ast
 */
Z3_ast tn_exist_uniqueOp_uniqueHeight(Z3_context ctx, const TunnelNetwork network, int length){
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

        // Au moins un
        Z3_ast existence = Z3_mk_or(ctx, num_vars, vars);
        
        // Au plus un (exclusion mutuelle par paires)
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
 * @brief φ2 : Pile initiale et finale
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
 * @brief φ3 : Règle de transition de hauteur pour la Transmission
 * 
 * @param length The length of the sought path.
 * @param pos The current position of the path.
 * @return Z3_ast
 */
// NÉCESSITE D'ÊTRE DÉCLARÉ DANS LE .H AVEC : (Z3_context, TunnelNetwork, int, int)
Z3_ast tn_transition_stack_height(Z3_context ctx, TunnelNetwork network, int length, int pos){
    int stack_size = get_stack_size(length);
    int num_nodes = tn_get_num_nodes(network);
    Z3_ast *constraints = malloc(num_nodes * stack_size * sizeof(Z3_ast));
    int count = 0;

    Z3_ast next_any_h[stack_size];
    for(int h=0; h<stack_size; h++) next_any_h[h] = tn_any_node_at(ctx, num_nodes, pos+1, h);

    for (int h = 0; h < stack_size; h++) {
        for (int u = 0; u < num_nodes; u++) {
            // Prémisse : On est en u à h, et au pas suivant on est ENCORE à h (Transmission)
            Z3_ast premise = Z3_mk_and(ctx, 2, (Z3_ast[]){
                tn_path_variable(ctx, u, pos, h),
                next_any_h[h] 
            });

            Z3_ast y4 = tn_4_variable(ctx, pos, h);
            Z3_ast y6 = tn_6_variable(ctx, pos, h);
            
            // Vérifie les capacités du nœud u dans le graphe
            Z3_ast can_t4 = tn_node_has_action(network, u, transmit_4) ? Z3_mk_true(ctx) : Z3_mk_false(ctx);
            Z3_ast can_t6 = tn_node_has_action(network, u, transmit_6) ? Z3_mk_true(ctx) : Z3_mk_false(ctx);

            Z3_ast valid_4 = Z3_mk_implies(ctx, y4, can_t4);
            Z3_ast valid_6 = Z3_mk_implies(ctx, y6, can_t6);

            Z3_ast conclusion = Z3_mk_and(ctx, 2, (Z3_ast[]){valid_4, valid_6});
            constraints[count++] = Z3_mk_implies(ctx, premise, conclusion);
        }
    }
    Z3_ast res = Z3_mk_and(ctx, count, constraints);
    free(constraints);
    return res;
}

/**
 * @brief φ4 : Règle de transition de hauteur pour l'encapsulation
 * 
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast
 */
// NÉCESSITE D'ÊTRE DÉCLARÉ DANS LE .H AVEC : (Z3_context, TunnelNetwork, int, int)
Z3_ast tn_encapsulation_stack_height(Z3_context ctx, TunnelNetwork network, int length, int pos){
    int stack_size = get_stack_size(length);
    if (stack_size <= 1) return Z3_mk_true(ctx);
    int num_nodes = tn_get_num_nodes(network);
    
    Z3_ast *constraints = malloc(num_nodes * (stack_size-1) * sizeof(Z3_ast));
    int count = 0;

    Z3_ast next_any_h_plus[stack_size];
    for(int h=0; h<stack_size-1; h++) next_any_h_plus[h] = tn_any_node_at(ctx, num_nodes, pos+1, h+1);

    for (int h = 0; h < stack_size - 1; h++) {
        for(int u=0; u < num_nodes; u++) {
            // Prémisse : On est en u à h, et au pas suivant on est à h+1 (Push)
            Z3_ast premise = Z3_mk_and(ctx, 2, (Z3_ast[]){
                tn_path_variable(ctx, u, pos, h),
                next_any_h_plus[h]
            });

            Z3_ast y4_curr = tn_4_variable(ctx, pos, h);
            Z3_ast y6_curr = tn_6_variable(ctx, pos, h);
            Z3_ast y4_next = tn_4_variable(ctx, pos+1, h+1);
            Z3_ast y6_next = tn_6_variable(ctx, pos+1, h+1);

            // On vérifie quelle action de PUSH est autorisée par le nœud u
            Z3_ast c1 = Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, (Z3_ast[]){y4_curr, y4_next}), 
                        tn_node_has_action(network, u, push_4_4) ? Z3_mk_true(ctx) : Z3_mk_false(ctx));
            Z3_ast c2 = Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, (Z3_ast[]){y4_curr, y6_next}), 
                        tn_node_has_action(network, u, push_4_6) ? Z3_mk_true(ctx) : Z3_mk_false(ctx));
            Z3_ast c3 = Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, (Z3_ast[]){y6_curr, y4_next}), 
                        tn_node_has_action(network, u, push_6_4) ? Z3_mk_true(ctx) : Z3_mk_false(ctx));
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
 * @brief φ5 : Règle de transition de hauteur pour la décapsulation
 * 
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast
 */
// NÉCESSITE D'ÊTRE DÉCLARÉ DANS LE .H AVEC : (Z3_context, TunnelNetwork, int, int)
Z3_ast tn_decapsulation_stack_height(Z3_context ctx, TunnelNetwork network, int length, int pos)
{
    int stack_size = get_stack_size(length);
    if (stack_size <= 1) return Z3_mk_true(ctx);
    int num_nodes = tn_get_num_nodes(network);

    Z3_ast *constraints = malloc(num_nodes * (stack_size-1) * sizeof(Z3_ast));
    int count = 0;

    Z3_ast next_any_h_minus[stack_size];
    for(int h=1; h<stack_size; h++) next_any_h_minus[h] = tn_any_node_at(ctx, num_nodes, pos+1, h-1);

    for (int h = 1; h < stack_size; h++) {
        for(int u=0; u < num_nodes; u++) {
            // Prémisse : On est en u à h, et au pas suivant on est à h-1 (Pop)
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
            
            // Cas 2: Top 4, Under 6 (64↓6) -> C'est pop_6_4 (on enlève 4 pour révéler 6)
            Z3_ast c2 = Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, (Z3_ast[]){y4_top, y6_under}), 
                        tn_node_has_action(network, u, pop_6_4) ? Z3_mk_true(ctx) : Z3_mk_false(ctx));
            
            // Cas 3: Top 6, Under 4 (46↓4) -> C'est pop_4_6 (on enlève 6 pour révéler 4)
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
 * @brief φ6 : Cohérence du contenu de pile (exactement avec un protocole (4 ou 6)
 * 
 * @param ctx The solver context.
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast 
 */
Z3_ast tn_stack_content_coherence(Z3_context ctx, int length, int pos)
{
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
 * @brief φ7 : Conditions nécessaires pour qu'une opération soit réalisable
 * 
 * @param ctx The solver context.
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast 
 */
// NÉCESSITE D'ÊTRE DÉCLARÉ DANS LE .H AVEC : (Z3_context, TunnelNetwork, int, int)
// φ7 : Faisabilité 
Z3_ast tn_operation_feasibility(Z3_context ctx, TunnelNetwork network, int length, int pos){
    int stack_size = get_stack_size(length);
    int num_nodes = tn_get_num_nodes(network);
    Z3_ast *constraints = malloc(num_nodes * stack_size * sizeof(Z3_ast));
    int count = 0;

    for(int h=0; h<stack_size; h++) {
        for(int u=0; u<num_nodes; u++) {
            Z3_ast active = tn_path_variable(ctx, u, pos, h);
            Z3_ast y4 = tn_4_variable(ctx, pos, h);
            Z3_ast y6 = tn_6_variable(ctx, pos, h);

            // CORRECTION: On doit vérifier l'action par rapport à ce qu'elle accepte en SOMMET (Top)
            
            // Actions acceptant un 4 au sommet
            bool can_input_4 = tn_node_has_action(network, u, transmit_4) ||
                               tn_node_has_action(network, u, push_4_4) ||
                               tn_node_has_action(network, u, push_4_6) ||
                               tn_node_has_action(network, u, pop_4_4) ||
                               tn_node_has_action(network, u, pop_6_4); // pop_6_4 signifie Top=4, Under=6

            // Actions acceptant un 6 au sommet
            bool can_input_6 = tn_node_has_action(network, u, transmit_6) ||
                               tn_node_has_action(network, u, push_6_4) ||
                               tn_node_has_action(network, u, push_6_6) ||
                               tn_node_has_action(network, u, pop_4_6) || // pop_4_6 signifie Top=6, Under=4
                               tn_node_has_action(network, u, pop_6_6);
            
            if (!can_input_4) {
                constraints[count++] = Z3_mk_implies(ctx, active, Z3_mk_not(ctx, y4));
            }
            if (!can_input_6) {
                constraints[count++] = Z3_mk_implies(ctx, active, Z3_mk_not(ctx, y6));
            }
        }
    }
    Z3_ast res = Z3_mk_and(ctx, count, constraints);
    free(constraints);
    return res;
}

//---------------------------------------------------------------------------------------------------------
//le bas de la pile est identique
Z3_ast tn_prefix_equal(Z3_context ctx, int pos, int next_pos, int limit)
{
    if (limit <= 0) {
        return Z3_mk_true(ctx); // rien à préserver → vrai
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

//Transmission : hauteur h → h
Z3_ast tn_stack_preservation_transmission(Z3_context ctx, int num_nodes, int pos, int h) 
{
    Z3_ast any_at_h = tn_any_node_at(ctx, num_nodes, pos,   h);
    Z3_ast next_at_h = tn_any_node_at(ctx, num_nodes, pos+1, h);
    Z3_ast trans_cond = Z3_mk_and(ctx, 2, (Z3_ast[]){ any_at_h, next_at_h });

    // On préserve les cases 0..h-1
    Z3_ast trans_preserves = tn_prefix_equal(ctx, pos, pos+1, h);

    return Z3_mk_implies(ctx, trans_cond, trans_preserves);
}

//hauteur h → h+1
Z3_ast tn_stack_preservation_encapsulation(Z3_context ctx, int num_nodes, int stack_size, int pos, int h) 
{
    Z3_ast any_at_h = tn_any_node_at(ctx, num_nodes, pos, h);
    Z3_ast next_at_h_plus = Z3_mk_false(ctx);

    if (h + 1 < stack_size) {
        next_at_h_plus = tn_any_node_at(ctx, num_nodes, pos+1, h+1);
    }

    Z3_ast enc_cond = Z3_mk_and(ctx, 2, (Z3_ast[]){ any_at_h, next_at_h_plus });

    // On préserve les cases 0..h (donc h+1 cases au total)
    Z3_ast enc_preserves = tn_prefix_equal(ctx, pos, pos+1, h+1);

    return Z3_mk_implies(ctx, enc_cond, enc_preserves);
}

//hauteur h → h-1
Z3_ast tn_stack_preservation_decapsulation(Z3_context ctx, int num_nodes, int pos, int h) 
{
    Z3_ast any_at_h = tn_any_node_at(ctx, num_nodes, pos,   h);
    Z3_ast next_at_h_minus = Z3_mk_false(ctx);

    if (h - 1 >= 0) {
        next_at_h_minus = tn_any_node_at(ctx, num_nodes, pos+1, h-1);
    }

    Z3_ast dec_cond = Z3_mk_and(ctx, 2, (Z3_ast[]){ any_at_h, next_at_h_minus });

    // On préserve les cases 0..h-1
    Z3_ast dec_preserves = tn_prefix_equal(ctx, pos, pos+1, h);

    return Z3_mk_implies(ctx, dec_cond, dec_preserves);
}

// --- Nouvelle Fonction Globale de Préservation de Pile ---
// Remplace les 3 fonctions ci-dessus.
Z3_ast tn_stack_preservation_logic(Z3_context ctx, const TunnelNetwork network, int length)
{
    int stack_size = get_stack_size(length);
    int num_nodes  = tn_get_num_nodes(network);
    int num_pos    = length;

    Z3_ast *constraints = malloc(num_pos * sizeof(Z3_ast));

    for (int pos = 0; pos < num_pos - 1; pos++) {  // attention : pos+1 utilisé !
        Z3_ast *h_constraints = malloc(stack_size * sizeof(Z3_ast));

        for (int h = 0; h < stack_size; h++) {

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

    // Pour la dernière position (pos = num_pos-1), tu peux soit :
    // - ne rien imposer (Z3_mk_true)
    // - ou gérer un cas particulier si besoin
    constraints[num_pos - 1] = Z3_mk_true(ctx);

    Z3_ast res = Z3_mk_and(ctx, num_pos, constraints);
    free(constraints);
    return res;
}
//------------------------------------------------------------------------------------------------------------------

/**
 * @brief edge_node : contrainte locale pour un nœud u à une position et une hauteur données.
 * Si on est à (u, pos, h), alors à pos+1 on doit être dans un successeur de u
 * (avec hauteur h, h+1 ou h-1).
 */
static Z3_ast tn_edge_node_constraint(Z3_context ctx, const TunnelNetwork network, int length, int pos, int h, int u)
{
    int num_nodes  = tn_get_num_nodes(network);
    int stack_size = get_stack_size(length);

    Z3_ast current = tn_path_variable(ctx, u, pos, h);

    // Liste des futurs possibles
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
        // Aucun successeur possible : on interdit d'être sur (u,pos,h)
        result = Z3_mk_not(ctx, current);
    } else {
        Z3_ast valid_or = Z3_mk_or(ctx, v_count, valid_next);
        result = Z3_mk_implies(ctx, current, valid_or);
    }

    free(valid_next);
    return result;
}

/**
 * @brief edge_height : contrainte pour toutes les valeurs de u à une hauteur h donnée.
 * Construit ∧_u edge_node(u, pos, h).
 */
static Z3_ast tn_edge_height_constraint(Z3_context ctx, const TunnelNetwork network, int length, int pos, int h)
{
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
 * @brief edge_pos : contrainte pour une position donnée (toutes les hauteurs)
 * Construit ∧_h edge_height(pos, h).
 */
static Z3_ast tn_edge_pos_constraint(Z3_context ctx, const TunnelNetwork network, int length, int pos)
{
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
 * @brief edge : si on est à (u, pos, h), alors à pos+1 on doit être dans un successeur de u
 * @param ctx The solver context.
 * @param network The graph
 * @param length The length of the sought path.
 * @return Z3_ast
 */

Z3_ast tn_edge_constraints(Z3_context ctx, const TunnelNetwork network, int length)
{
    int num_pos = length; // on va de pos = 0 à length-1
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
Z3_ast tn_reduction(Z3_context ctx, const TunnelNetwork network, int length)
{
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

    // Préservation de pile (remplace f8, f9, f10)
    Z3_ast f_preservation = tn_stack_preservation_logic(ctx, network, length);

    // Edges
    Z3_ast f_edges = tn_edge_constraints(ctx, network, length);

    // FIX: Array size is 9 now
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
