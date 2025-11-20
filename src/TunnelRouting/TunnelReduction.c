#include "TunnelReduction.h"
#include "Z3Tools.h"
#include "stdio.h"
#include <stdlib.h>

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

    int num_positions = length + 1;  // 0..length

    Z3_ast *pos_constraints = malloc(num_positions * sizeof(Z3_ast));

    for (int i = 0; i <= length; i++) {
        // 1) Liste de toutes les variables x_{op,i,h}
        Z3_ast *vars = malloc(num_vars * sizeof(Z3_ast));
        int idx = 0;
        for (int h = 0; h < stack_size; h++) {
            for (int op = 0; op < num_nodes; op++) {
                vars[idx++] = tn_path_variable(ctx, op, i, h);
            }
        }

        // 2) "Au moins une"
        Z3_ast existence = Z3_mk_or(ctx, num_vars, vars);

        // 3) "Au plus une"
        int num_pairs = num_vars * (num_vars - 1) / 2;
        Z3_ast *clauses = malloc(num_pairs * sizeof(Z3_ast));
        int c = 0;
        for (int p = 0; p < num_vars; p++) {
            for (int q = p + 1; q < num_vars; q++) {
                Z3_ast not_both[2] = {
                    Z3_mk_not(ctx, vars[p]),
                    Z3_mk_not(ctx, vars[q])
                };
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
Z3_ast tn_transition_stack_height(Z3_context ctx, int length, int pos){
    int stack_size = get_stack_size(length);

    Z3_ast *constraints = malloc(stack_size * sizeof(Z3_ast));

    for (int h = 0; h < stack_size; h++) {

        // conditions : x_{0,pos,h} ∨ x_{1,pos,h}
        Z3_ast cond[2] = {
            tn_path_variable(ctx, 0, pos, h),
            tn_path_variable(ctx, 1, pos, h)
        };
        Z3_ast condition = Z3_mk_or(ctx, 2, cond);

        // Si on transmet à la position pos avec hauteur h, alors à la position pos+1, la hauteur doit rester h.
        Z3_ast *at_next = malloc(10 * sizeof(Z3_ast));
        for (int op = 0; op < 10; op++) {
            at_next[op] = tn_path_variable(ctx, op, pos + 1, h);
        }
        Z3_ast next_height_ok = Z3_mk_or(ctx, 10, at_next);

        // implication
        constraints[h] = Z3_mk_implies(ctx, condition, next_height_ok);

        free(at_next);
    }

    Z3_ast result = Z3_mk_and(ctx, stack_size, constraints);
    free(constraints);
    return result;
}


/**
 * @brief φ4 : Règle de transition de hauteur pour l'encapsulation
 * 
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast
 */
Z3_ast tn_encapsulation_stack_height(Z3_context ctx, int length, int pos){
    int stack_size = get_stack_size(length);

    // si la pile est trop petite, aucun push possible
    if (stack_size <= 1) {
        return Z3_mk_true(ctx);
    }

    // on aura une contrainte par hauteur h : 0..stack_size-2
    int num_heights = stack_size - 1;
    Z3_ast *constraints = malloc(num_heights * sizeof(Z3_ast));

    for (int h = 0; h < num_heights; h++) {

        // prémisse : "on fait un push à (pos,h)"
        // x_{2,pos,h} ∨ x_{3,pos,h} ∨ x_{4,pos,h} ∨ x_{5,pos,h}
        Z3_ast prem[4] = {
            tn_path_variable(ctx, 2, pos, h),
            tn_path_variable(ctx, 3, pos, h),
            tn_path_variable(ctx, 4, pos, h),
            tn_path_variable(ctx, 5, pos, h)
        };
        Z3_ast premise = Z3_mk_or(ctx, 4, prem);

        // conclusion :
        //  ∨_{op=0..9} x_{op,pos+1,h+1}
        Z3_ast *at_next = malloc(10 * sizeof(Z3_ast));
        for (int op = 0; op < 10; op++) {
            at_next[op] = tn_path_variable(ctx, op, pos + 1, h + 1);
        }
        Z3_ast next_height_ok = Z3_mk_or(ctx, 10, at_next);

        // implication : (push à h) ⇒ (hauteur h+1 au pas suivant)
        constraints[h] = Z3_mk_implies(ctx, premise, next_height_ok);

        free(at_next);
    }

    Z3_ast result = Z3_mk_and(ctx, num_heights, constraints);
    free(constraints);
    return result;
}

/**
 * @brief φ5 : Règle de transition de hauteur pour la décapsulation
 * 
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast
 */
Z3_ast tn_decapsulation_stack_height(Z3_context ctx, int length, int pos)
{
    int stack_size = get_stack_size(length);

    // on ne peut décapsuler que si la pile a au moins 2 cases
    if (stack_size <= 1) {
        return Z3_mk_true(ctx);
    }

    int decap_ops[] = {6, 7, 8, 9};
    int nb_decap_ops = 4;

    int num_heights = stack_size - 1;           // h = 1..stack_size-1
    Z3_ast *constraints = malloc(num_heights * sizeof(Z3_ast));

    for (int h = 1; h < stack_size; h++) {

        // condition : on fait une opération de décapsulation à (pos, h)
        Z3_ast cond[nb_decap_ops];
        for (int i = 0; i < nb_decap_ops; i++) {
            cond[i] = tn_path_variable(ctx, decap_ops[i], pos, h);
        }
        Z3_ast premise = Z3_mk_or(ctx, nb_decap_ops, cond);

        //à pos+1, la hauteur devient h-1 (quelque soit l'op)
        Z3_ast *at_next = malloc(10 * sizeof(Z3_ast));
        for (int op = 0; op < 10; op++) {
            at_next[op] = tn_path_variable(ctx, op, pos + 1, h - 1);
        }
        Z3_ast next_height_ok = Z3_mk_or(ctx, 10, at_next);

        constraints[h - 1] = Z3_mk_implies(ctx, premise, next_height_ok);

        free(at_next);
    }

    Z3_ast result = Z3_mk_and(ctx, num_heights, constraints);
    free(constraints);
    return result;
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

        // "il y a un état à la hauteur h"
        Z3_ast nodes_here[10];
        for (int op = 0; op < 10; op++) {
            nodes_here[op] = tn_path_variable(ctx, op, pos, h);
        }
        Z3_ast node_here = Z3_mk_or(ctx, 10, nodes_here);

        // variables de contenu de pile
        Z3_ast y4 = tn_4_variable(ctx, pos, h);
        Z3_ast y6 = tn_6_variable(ctx, pos, h);

        // XOR : exactement un de y4, y6 est vrai
        Z3_ast at_least_one = Z3_mk_or(ctx, 2, (Z3_ast[]){ y4, y6 });
        Z3_ast at_most_one  = Z3_mk_or(ctx, 2, (Z3_ast[]){
            Z3_mk_not(ctx, y4),
            Z3_mk_not(ctx, y6)
        });
        Z3_ast exactly_one = Z3_mk_and(ctx, 2, (Z3_ast[]){ at_least_one, at_most_one });

        // si on a un état à cette hauteur, alors exactement un protocole
        constraints[h] = Z3_mk_implies(ctx, node_here, exactly_one);
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
Z3_ast tn_operation_feasibility(Z3_context ctx, int length, int pos){
    int stack_size = get_stack_size(length);
    if (stack_size == 0) {
        return Z3_mk_true(ctx);
    }
    int nodes_for_4[] = {0, 2, 4, 6, 8};
    int nb_nodes_for_4 = 5;

    int nodes_for_6[] = {1, 3, 5, 7, 9};
    int nb_nodes_for_6 = 5;

    // une pour 4, une pour 6
    Z3_ast constraints[2 * stack_size];
    int k = 0;
    for (int h = 0; h < stack_size; h++) {
    
        // cas a = 4
        Z3_ast conditions_4[nb_nodes_for_4];
        for (int i = 0; i < nb_nodes_for_4; i++) {
            conditions_4[i] = tn_path_variable(ctx, nodes_for_4[i], pos, h);
        }
        Z3_ast condition_4 = Z3_mk_or(ctx, nb_nodes_for_4, conditions_4);
        Z3_ast y4 = tn_4_variable(ctx, pos, h);
        constraints[k++] = Z3_mk_implies(ctx, condition_4, y4);

        // cas a = 6
        Z3_ast conditions_6[nb_nodes_for_6];
        for (int i = 0; i < nb_nodes_for_6; i++) {
            conditions_6[i] = tn_path_variable(ctx, nodes_for_6[i], pos, h);
        }
        Z3_ast condition_6 = Z3_mk_or(ctx, nb_nodes_for_6, conditions_6);
        Z3_ast y6 = tn_6_variable(ctx, pos, h);
        constraints[k++] = Z3_mk_implies(ctx, condition_6, y6);
    }
    return Z3_mk_and(ctx, k, constraints);
}

/**
 * @brief φ8 : Evolution du contenu de la pile lors d'une transmission
 *        Si on transmet à (pos, h) (opérations 0 ou 1), alors pour toutes
 *        les hauteurs k < h, le contenu de pile (4/6) reste identique
 *        entre pos et pos+1.
 *
 * @param ctx The solver context.
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast
 */
Z3_ast tn_stack_content_transmission(Z3_context ctx, int length, int pos)
{
    int stack_size = get_stack_size(length);

    if (stack_size == 0) {
        return Z3_mk_true(ctx);
    }

    Z3_ast *constraints = malloc(stack_size * sizeof(Z3_ast));

    for (int h = 0; h < stack_size; h++) {

        // condition : on fait une transmission à (pos,h)
        // (opérations 0 et 1)
        Z3_ast cond_ops[2] = {
            tn_path_variable(ctx, 0, pos, h),
            tn_path_variable(ctx, 1, pos, h)
        };
        Z3_ast premise = Z3_mk_or(ctx, 2, cond_ops);

        Z3_ast conclusion;

        if (h == 0) {
            // ∧_{k=0}^{-1} (...) = vrai : pas de cellule en dessous
            conclusion = Z3_mk_true(ctx);
        } else {
            // k = 0 .. h-1  (donc h valeurs)
            int num_k = h;
            Z3_ast *eq_for_all_k = malloc(num_k * sizeof(Z3_ast));

            for (int k = 0; k < h; k++) {

                Z3_ast y4_now  = tn_4_variable(ctx, pos,     k);
                Z3_ast y4_next = tn_4_variable(ctx, pos + 1, k);
                Z3_ast y6_now  = tn_6_variable(ctx, pos,     k);
                Z3_ast y6_next = tn_6_variable(ctx, pos + 1, k);

                Z3_ast eq4 = Z3_mk_iff(ctx, y4_now,  y4_next);
                Z3_ast eq6 = Z3_mk_iff(ctx, y6_now,  y6_next);

                eq_for_all_k[k] = Z3_mk_and(ctx, 2, (Z3_ast[]){ eq4, eq6 });
            }

            conclusion = Z3_mk_and(ctx, num_k, eq_for_all_k);
            free(eq_for_all_k);
        }

        constraints[h] = Z3_mk_implies(ctx, premise, conclusion);
    }

    Z3_ast result = Z3_mk_and(ctx, stack_size, constraints);
    free(constraints);
    return result;
}

/**
 * @brief φ9 : Evolution du contenu de la pile lors d'une encapsulation
 *        Si on encapsule à (pos, h) (opérations 2, 3, 4 ou 5),
 *        alors pour toutes les hauteurs k ≤ h, le contenu de pile (4/6)
 *        reste identique entre pos et pos+1.
 *
 * @param ctx The solver context.
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast
 */
Z3_ast tn_stack_content_encapsulation(Z3_context ctx, int length, int pos)
{
    int stack_size = get_stack_size(length);

    // pile trop petite -> pas de push possible
    if (stack_size <= 1) {
        return Z3_mk_true(ctx);
    }

    // on ne peut pousser que de h = 0 à stack_size-2
    int num_heights = stack_size - 1;
    Z3_ast *constraints = malloc(num_heights * sizeof(Z3_ast));

    for (int h = 0; h < num_heights; h++) {

        // condition : on fait une encapsulation à (pos,h)
        // opérations 2, 3, 4, 5
        Z3_ast cond_ops[4] = {
            tn_path_variable(ctx, 2, pos, h),
            tn_path_variable(ctx, 3, pos, h),
            tn_path_variable(ctx, 4, pos, h),
            tn_path_variable(ctx, 5, pos, h)
        };
        Z3_ast premise = Z3_mk_or(ctx, 4, cond_ops);

        // conclusion :
        // pour tout k = 0..h, y4(pos,k) <-> y4(pos+1,k)
        // et y6(pos,k) <-> y6(pos+1,k)
        int num_k = h + 1; // k = 0..h
        Z3_ast *eq_for_all_k = malloc(num_k * sizeof(Z3_ast));

        for (int k = 0; k <= h; k++) {

            Z3_ast y4_now  = tn_4_variable(ctx, pos,     k);
            Z3_ast y4_next = tn_4_variable(ctx, pos + 1, k);
            Z3_ast y6_now  = tn_6_variable(ctx, pos,     k);
            Z3_ast y6_next = tn_6_variable(ctx, pos + 1, k);

            Z3_ast eq4 = Z3_mk_iff(ctx, y4_now,  y4_next);
            Z3_ast eq6 = Z3_mk_iff(ctx, y6_now,  y6_next);

            eq_for_all_k[k] = Z3_mk_and(ctx, 2, (Z3_ast[]){ eq4, eq6 });
        }

        Z3_ast conclusion = Z3_mk_and(ctx, num_k, eq_for_all_k);
        free(eq_for_all_k);

        constraints[h] = Z3_mk_implies(ctx, premise, conclusion);
    }

    Z3_ast result = Z3_mk_and(ctx, num_heights, constraints);
    free(constraints);
    return result;
}

/**
 * @brief φ10 : Evolution du contenu de la pile lors d'une décapsulation
 *        Si on décapsule à (pos, h) (opérations 6, 7, 8 ou 9),
 *        alors pour toutes les hauteurs k < h, le contenu de pile (4/6)
 *        reste identique entre pos et pos+1.
 *
 * @param ctx The solver context.
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast
 */
Z3_ast tn_stack_content_decapsulation(Z3_context ctx, int length, int pos)
{
    int stack_size = get_stack_size(length);

    // il faut au moins une pile de hauteur >= 1 pour pouvoir pop
    if (stack_size <= 1) {
        return Z3_mk_true(ctx);
    }

    // on ne peut décapsuler qu'à partir de h = 1
    int num_heights = stack_size - 1; // h = 1..stack_size-1
    Z3_ast *constraints = malloc(num_heights * sizeof(Z3_ast));

    for (int h = 1; h < stack_size; h++) {

        // condition : on fait une décapsulation à (pos,h)
        // opérations 6, 7, 8, 9
        Z3_ast cond_ops[4] = {
            tn_path_variable(ctx, 6, pos, h),
            tn_path_variable(ctx, 7, pos, h),
            tn_path_variable(ctx, 8, pos, h),
            tn_path_variable(ctx, 9, pos, h)
        };
        Z3_ast premise = Z3_mk_or(ctx, 4, cond_ops);

        Z3_ast conclusion;

        if (h == 0) {
            // ne devrait pas arriver car on commence à h=1,
            // mais par sécurité :
            conclusion = Z3_mk_true(ctx);
        } else {
            // pour tout k = 0..h-1,
            // y4(pos,k) <-> y4(pos+1,k)
            // y6(pos,k) <-> y6(pos+1,k)
            int num_k = h; // k = 0..h-1
            Z3_ast *eq_for_all_k = malloc(num_k * sizeof(Z3_ast));

            for (int k = 0; k < h; k++) {

                Z3_ast y4_now  = tn_4_variable(ctx, pos,     k);
                Z3_ast y4_next = tn_4_variable(ctx, pos + 1, k);
                Z3_ast y6_now  = tn_6_variable(ctx, pos,     k);
                Z3_ast y6_next = tn_6_variable(ctx, pos + 1, k);

                Z3_ast eq4 = Z3_mk_iff(ctx, y4_now,  y4_next);
                Z3_ast eq6 = Z3_mk_iff(ctx, y6_now,  y6_next);

                eq_for_all_k[k] = Z3_mk_and(ctx, 2, (Z3_ast[]){ eq4, eq6 });
            }

            conclusion = Z3_mk_and(ctx, num_k, eq_for_all_k);
            free(eq_for_all_k);
        }

        constraints[h - 1] = Z3_mk_implies(ctx, premise, conclusion);
    }

    Z3_ast result = Z3_mk_and(ctx, num_heights, constraints);
    free(constraints);
    return result;
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
    int num_pos = length;                //0..length-1
    int stack_size = get_stack_size(length);
    int num_nodes = tn_get_num_nodes(network);

    Z3_ast *pos_constraints = malloc(num_pos * sizeof(Z3_ast));

    for (int pos = 0; pos < num_pos; pos++) {

        Z3_ast *height_constraints = malloc(stack_size * sizeof(Z3_ast));

        for (int h = 0; h < stack_size; h++) {

            Z3_ast *node_constraints = malloc(num_nodes * sizeof(Z3_ast));

            for (int u = 0; u < num_nodes; u++) {

                // collecte toutes les successeurs v ode u
                Z3_ast *succs = malloc(num_nodes * sizeof(Z3_ast));
                int succ_count = 0;

                for (int v = 0; v < num_nodes; v++) {
                    if (tn_is_edge(network, u, v)) {
                        succs[succ_count++] = tn_path_variable(ctx, v, pos + 1, h);
                    }
                }

                Z3_ast implication;

                if (succ_count == 0) {
                    // pas de successeur, ne peut pas etre à u à pos,h
                    implication = Z3_mk_not(ctx, tn_path_variable(ctx, u, pos, h));
                } else {
                    Z3_ast succ_or = Z3_mk_or(ctx, succ_count, succs);
                    implication = Z3_mk_implies(
                        ctx,
                        tn_path_variable(ctx, u, pos, h),
                        succ_or
                    );
                }

                node_constraints[u] = implication;
                free(succs);
            }

            height_constraints[h] =
                Z3_mk_and(ctx, num_nodes, node_constraints);
            free(node_constraints);
        }

        pos_constraints[pos] =
            Z3_mk_and(ctx, stack_size, height_constraints);
        free(height_constraints);
    }

    Z3_ast result = Z3_mk_and(ctx, num_pos, pos_constraints);
    free(pos_constraints);
    return result;
}

Z3_ast tn_reduction(Z3_context ctx, const TunnelNetwork network, int length)
{
    // φ1 : existence + unicité (node, hauteur) à chaque position
    Z3_ast f1 = tn_exist_uniqueOp_uniqueHeight(ctx, network, length);

    // φ2 : pile initiale et finale
    Z3_ast f2 = tn_init_final_stack(ctx, network, length);

    // φ3 : transmission (hauteur inchangée)
    Z3_ast *f3_parts = malloc(length * sizeof(Z3_ast));
    for (int pos = 0; pos < length; pos++) {
        f3_parts[pos] = tn_transition_stack_height(ctx, length, pos);
    }
    Z3_ast f3 = Z3_mk_and(ctx, length, f3_parts);
    free(f3_parts);

    // φ4 : encapsulation (push, h -> h+1)
    Z3_ast *f4_parts = malloc(length * sizeof(Z3_ast));
    for (int pos = 0; pos < length; pos++) {
        f4_parts[pos] = tn_encapsulation_stack_height(ctx, length, pos);
    }
    Z3_ast f4 = Z3_mk_and(ctx, length, f4_parts);
    free(f4_parts);

    // φ5 : décapsulation (pop, h -> h-1)
    Z3_ast *f5_parts = malloc(length * sizeof(Z3_ast));
    for (int pos = 0; pos < length; pos++) {
        f5_parts[pos] = tn_decapsulation_stack_height(ctx, length, pos);
    }
    Z3_ast f5 = Z3_mk_and(ctx, length, f5_parts);
    free(f5_parts);

    // φ6 : cohérence du contenu de pile
    // positions 0..length (donc length+1 positions)
    int num_pos_stack = length + 1;
    Z3_ast *f6_parts = malloc(num_pos_stack * sizeof(Z3_ast));
    for (int pos = 0; pos <= length; pos++) {
        f6_parts[pos] = tn_stack_content_coherence(ctx, length, pos);
    }
    Z3_ast f6 = Z3_mk_and(ctx, num_pos_stack, f6_parts);
    free(f6_parts);

    // φ7 : conditions de faisabilité des opérations (liées à y4 / y6)
    Z3_ast *f7_parts = malloc(length * sizeof(Z3_ast));
    for (int pos = 0; pos < length; pos++) {
        f7_parts[pos] = tn_operation_feasibility(ctx, length, pos);
    }
    Z3_ast f7 = Z3_mk_and(ctx, length, f7_parts);
    free(f7_parts);

    // φ8 : évolution du contenu de pile lors des transmissions
    Z3_ast *f8_parts = malloc(length * sizeof(Z3_ast));
    for (int pos = 0; pos < length; pos++) {
        f8_parts[pos] = tn_stack_content_transmission(ctx, length, pos);
    }
    Z3_ast f8 = Z3_mk_and(ctx, length, f8_parts);
    free(f8_parts);

    // φ9 : encapsulation (contenu de pile)
    Z3_ast *f9_parts = malloc(length * sizeof(Z3_ast));
    for (int pos = 0; pos < length; pos++) {
        f9_parts[pos] = tn_stack_content_encapsulation(ctx, length, pos);
    }
    Z3_ast f9 = Z3_mk_and(ctx, length, f9_parts);
    free(f9_parts);

    // φ10 : décapsulation (contenu de pile)
    Z3_ast *f10_parts = malloc(length * sizeof(Z3_ast));
    for (int pos = 0; pos < length; pos++) {
        f10_parts[pos] = tn_stack_content_decapsulation(ctx, length, pos);
    }
    Z3_ast f10 = Z3_mk_and(ctx, length, f10_parts);
    free(f10_parts);

    // Contraintes d’arêtes du graphe
    Z3_ast f_edges = tn_edge_constraints(ctx, network, length);

    // Conjonction globale de toutes les formules
    Z3_ast all[11] = { f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f_edges };
    return Z3_mk_and(ctx, 11, all);
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