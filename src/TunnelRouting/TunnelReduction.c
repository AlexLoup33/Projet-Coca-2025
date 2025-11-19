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
 * @param length The length of the sought path.
 * @return Z3_ast
 */
Z3_ast tn_exist_uniqueOp_uniqueHeight(Z3_context ctx, int length){
    int stack_size = get_stack_size(length);
    int num_nodes = 10;
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
 * @param length The length of the sought path.
 * @return Z3_ast
 */
Z3_ast tn_init_final_stack(Z3_context ctx, int length){
    int stack_size = get_stack_size(length);

    Z3_ast init_stack = Z3_mk_and(ctx, 2, (Z3_ast[]){
        tn_path_variable(ctx, 0, 0, 0),
        tn_4_variable(ctx, 0, 0)
    });
    Z3_ast final_stack[stack_size];

    for (int op = 0; op < stack_size; op++){
        final_stack[op] = Z3_mk_and(ctx, 2, (Z3_ast[]){
            tn_path_variable(ctx, 0, length, 0),
            tn_4_variable(ctx, length, 0)
        });
    }

    Z3_ast final_stack_prop = Z3_mk_or(ctx, stack_size, final_stack);
    return Z3_mk_and(ctx, 2, (Z3_ast[]){init_stack, final_stack_prop});
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

    Z3_ast res[stack_size];
    for (int h = 0; h < stack_size; h++){
        Z3_ast transmit_neg[2];
        transmit_neg[0] = Z3_mk_not(ctx, tn_path_variable(ctx, 0, pos, h));
        transmit_neg[1] = Z3_mk_not(ctx, tn_path_variable(ctx, 1, pos, h));

        Z3_ast transmit_prop = Z3_mk_or(ctx, 2, transmit_neg);

        Z3_ast same_height[10];
        for (int op = 0; op < 10; op++){
            same_height[op] = tn_path_variable(ctx, op, pos+1, h);
        }
        Z3_ast same_height_prop = Z3_mk_or(ctx, 10, same_height);

        res[h] = Z3_mk_and(ctx, 2, (Z3_ast[]){transmit_prop, same_height_prop});
    }
    return Z3_mk_and(ctx, stack_size, res);
}

/**
 * @brief φ4 : Règle de transition de hauteur pour l'encapsulation
 * 
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast
 */
Z3_ast tn_encapsulation_stack_height(Z3_context ctx, int length, int pos){
    int stack_height = get_stack_size(length);

    Z3_ast res[stack_height];
    for (int h = 0; h < stack_height; h++){
        Z3_ast op_neg[stack_height*4];
        Z3_ast encapsulation[stack_height*10];

        for (int op = 6; op < 10; op++){
            op_neg[h*(op+1)] = Z3_mk_not(ctx, tn_path_variable(ctx, op, pos, h));
        }

        for (int op = 0; op < 10; op++){
            encapsulation[h*(op+1)] = tn_path_variable(ctx, op, pos+1, h+1);
        }
        Z3_ast op_neg_prop = Z3_mk_or(ctx, stack_height*4, op_neg);
        Z3_ast encapsulation_prop = Z3_mk_or(ctx, stack_height*10, encapsulation);
        res[h] = Z3_mk_and(ctx, 2, (Z3_ast[]){op_neg_prop, encapsulation_prop});
    }
    return Z3_mk_and(ctx, stack_height, res);
}

/**
 * @brief φ5 : Règle de transition de hauteur pour la décapsulation
 * 
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast
 */
Z3_ast tn_decapsulation_stack_height(Z3_context ctx, int length, int pos){
    int stack_heigth = get_stack_size(length);

    Z3_ast res[stack_heigth];
    for (int h = 1; h < stack_heigth; h++){
        Z3_ast op_neg[stack_heigth*4];
        Z3_ast decapsulation[stack_heigth*10];

        for (int op = 4; op < 8; op++){
            op_neg[(h-1)*(op+1)] = Z3_mk_not(ctx, tn_path_variable(ctx, op, pos, h));
        }

        for (int op = 0; op < 10; op++){
            decapsulation[(h-1)*(op+1)] = tn_path_variable(ctx, op, pos+1, h-1);
        }

        Z3_ast op_neg_prop = Z3_mk_or(ctx, stack_heigth*4, op_neg);
        Z3_ast decapsulation_prop = Z3_mk_or(ctx, stack_heigth*10, decapsulation);
        res[h-1] = Z3_mk_and(ctx, 2, (Z3_ast[]){op_neg_prop, decapsulation_prop});
    }
    return Z3_mk_and(ctx, stack_heigth-1, res);
}

/**
 * @brief φ6 : Cohérence du contenu de pile (exactement avec un protocole (4 ou 6)
 * 
 * @param ctx The solver context.
 * @param length The length of the sought path.
 * @param pos The current position in the path.
 * @return Z3_ast 
 */
Z3_ast tn_stack_content_coherence(Z3_context ctx, int length, int pos){
    int stack_size = get_stack_size(length);

    Z3_ast res[stack_size];
    for (int h = 0; h < stack_size; h++){
        Z3_ast not_exist_op[10];
        for (int op = 0; op < 10; op++){
            not_exist_op[op] = Z3_mk_not(ctx, tn_path_variable(ctx, op, pos, h));
        }

        Z3_ast stack_content[h];
        // Equivalence entre tn_4_variable et tn_6_variable pour argument h, pos
        for (int k = 0; k < h; k++){
            stack_content[k] = Z3_mk_and(ctx, 2, (Z3_ast[]){
                Z3_mk_or(ctx, 2, (Z3_ast[]){
                    Z3_mk_not(ctx, tn_4_variable(ctx, pos, k)),
                    tn_6_variable(ctx, pos, k)
                }),
                Z3_mk_or(ctx, 2, (Z3_ast[]){
                    tn_4_variable(ctx, pos, k),
                    Z3_mk_not(ctx, tn_6_variable(ctx, pos, k))
                })
            });
        }
        Z3_ast stack_content_prop = Z3_mk_and(ctx, h, stack_content);
        Z3_ast not_exist_op_prop = Z3_mk_or(ctx, 10, not_exist_op);
        res[h] = Z3_mk_and(ctx, 2, (Z3_ast[]){not_exist_op_prop, stack_content_prop});
    }
    return Z3_mk_and(ctx, stack_size, res);
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

Z3_ast tn_reduction(Z3_context ctx, const TunnelNetwork network, int length)
{
    return tn_exist_uniqueOp_uniqueHeight(ctx, length);
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