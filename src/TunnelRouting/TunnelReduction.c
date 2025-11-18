#include "TunnelReduction.h"
#include "Z3Tools.h"
#include "stdio.h"

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
 * @brief φ1 : Existence, unique opération et unique hauteur.
 * 
 * @param ctx The solver context.
 * @param length The length of the sought path.
 * @return Z3_ast
 */
Z3_ast tn_exist_uniqueOp_uniqueHeight(Z3_context ctx, int length){
    int stack_size = get_stack_size(length);

    Z3_ast left[length*stack_size*10];
    Z3_ast right[length*stack_size*stack_size*10*10];


    int indexL = 0;
    int indexR = 0;
    // Pour tout i de 0 à l
    for (unsigned int i = 0; i < length; i++){
        
        //Proposition de gauche

        // Il existe op E Op
        for (unsigned int op = 0; op < 10; op++){
            // Il existe h entre 0 et hmax
            for (unsigned int h = 0; h < stack_size; h++){
                left[indexL] = tn_path_variable(ctx, op, i, h);
                indexL++;
            }
        }

        int index = 0;
        // Proposition de droite
        for (unsigned op = 0; op < 10; op++){
            for (unsigned opP = 0; opP < 10; op++){
                for (unsigned int h = 0; h < stack_size; h++){
                    for (unsigned hP = 0; hP < stack_size; h++){
                        if ((op, h) != (opP, hP)){
                            right[indexR] = Z3_mk_or(ctx, 2, (Z3_ast[]){Z3_mk_not(ctx, tn_path_variable(ctx, op, i, h)), Z3_mk_not(ctx, tn_path_variable(ctx, opP, i, hP))});
                        }
                    }
                }
            }
        } 
    }

    Z3_ast left_prop = Z3_mk_or(ctx, indexL, left);
    Z3_ast right_prop = Z3_mk_and(ctx, indexR, right);

    return Z3_mk_and(ctx, 2, (Z3_ast[]){left_prop, right_prop});
}

/**
 * @brief φ2 : Pile initiale et finale
 * 
 * @param ctx The solver context.
 * @param length The length of the sought path.
 * @return Z3_ast
 */
Z3_ast tn_init_final_stack(Z3_context ctx, int length){
    Z3_mk_and(ctx, 2, (Z3_ast[]){tn_4_variable(ctx, 0, 0), tn_4_variable(ctx, length, 0)});
}

/**
 * @brief φ3 : Règle de transition de hauteur pour la Transmission
 * 
 * @param length The length of the sought path.
 * @param pos The current position of the path.
 * @return Z3_ast
 */
Z3_ast tn_transition_stack_height(Z3_context ctx, int length, int pos){
    int stack_height = get_stack_size(length);
    
    Z3_ast transition[stack_height*10];
    Z3_ast neg_op[stack_height*2];
    
    for (int h = 0; h <= stack_height; h++){
        for (int op = 0; op < 2; op++){
            transition[h*(op+1)] = Z3_mk_not(ctx, tn_path_variable(ctx, op, pos, h));
        }

        for (int op = 0; op < 10; op++){
            transition[h*(op+1)] = tn_path_variable(ctx, op, pos+1, h);
        }
    }

    Z3_ast transition_prop = Z3_mk_or(ctx, stack_height*10, transition);
    Z3_ast neg_op_prop = Z3_mk_or(ctx, stack_height*2, neg_op);

    return Z3_mk_or(ctx, 2, (Z3_ast[]){transition_prop, neg_op_prop});
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

    Z3_ast op_neg[stack_height*4];
    Z3_ast encapsulation[stack_height*10];

    for (int h = 0; h < stack_height; h++){
        for (int op = 2; op < 6; op++){
            op_neg[h*(op+1)] = Z3_mk_not(ctx, tn_path_variable(ctx, op, pos, stack_height));
        }

        for (int op = 0; op < 10; op++){
            encapsulation[h*(op+1)] = tn_path_variable(ctx, op, pos+1, h+1);
        }
    }

    Z3_ast op_neg_prop = Z3_mk_or(ctx, stack_height*4, op_neg);
    Z3_ast encapsulation_prop = Z3_mk_or(ctx, stack_height*10, encapsulation);

    return Z3_mk_and(ctx, 2, (Z3_ast[]){op_neg_prop, encapsulation_prop});
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

    Z3_ast op_neg[stack_heigth*4];
    Z3_ast decapsulation[stack_heigth*10];

    for (int h = 0; h < stack_heigth; h++){
        for (int op = 6; op < 10; op++){
            op_neg[h*(op+1)] = Z3_mk_not(ctx, tn_path_variable(op, op, pos, h));
        }

        for (int op = 0; op < 10; op++){
            decapsulation[h*(op+1)] = tn_path_variable(ctx, op, pos+1, h-1);
        }
    }

    Z3_ast op_neg_prop = Z3_mk_or(ctx, stack_heigth*4, op_neg);
    Z3_ast decapsulation_prop = Z3_mk_or(ctx, stack_heigth*10, decapsulation);

    return Z3_mk_and(ctx, 2, (Z3_ast[]){op_neg_prop, decapsulation_prop});
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

Z3_ast tn_reduction(Z3_context ctx, const TunnelNetwork network, int length)
{
    return tn_exist_uniqueOp_uniqueHeight(ctx, length, get_stack_size(length));
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