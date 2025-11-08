#include "TunnelNetwork.h"
#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <string.h>
#include <assert.h>

struct TunnelNetwork_s
{
    Graph graph;       ///< The graph supporting the network.
    int initial;       ///< The starting node of the network.
    int final;         ///< The target node of the network.
    int *node_actions; ///< The actions associated with nodes (uses a mask encoding).
};

TunnelNetwork tn_initialize(Graph graph)
{
    TunnelNetwork result = (TunnelNetwork)malloc(sizeof(*result));
    result->graph = graph;
    int num_nodes = graph_num_nodes(graph);
    result->node_actions = (int *)malloc(num_nodes * sizeof(int));
    result->initial = 0; // dummy value
    result->final = 0;   // dummy value
    for (int node = 0; node < num_nodes; node++)
    {
        char *param = parameter_list_get_value(graph_get_node_parameter(graph, node), "shape");
        if (param != NULL)
        {
            if (strcmp("square", param) == 0)
                result->initial = node;
            if (strcmp("invtriangle", param) == 0)
                result->final = node;
        }
        char *actions = parameter_list_get_value(graph_get_node_parameter(graph, node), "label");
        if (actions == NULL)
            continue;
        char work[strlen(actions) + 1];
        strcpy(work, actions);
        const char delim[] = "\\n\"";
        char *lex = NULL;
        char *token = strtok_r(work, delim, &lex);
        result->node_actions[node] = 0;
        while (token != NULL)
        {
            if (strcmp(token, "4→4") == 0)
                result->node_actions[node] += 1 << transmit_4;
            if (strcmp(token, "6→6") == 0)
                result->node_actions[node] += 1 << transmit_6;
            if (strcmp(token, "4↑44") == 0)
                result->node_actions[node] += 1 << push_4_4;
            if (strcmp(token, "4↑46") == 0)
                result->node_actions[node] += 1 << push_4_6;
            if (strcmp(token, "6↑64") == 0)
                result->node_actions[node] += 1 << push_6_4;
            if (strcmp(token, "6↑66") == 0)
                result->node_actions[node] += 1 << push_6_6;
            if (strcmp(token, "44↓4") == 0)
                result->node_actions[node] += 1 << pop_4_4;
            if (strcmp(token, "46↓4") == 0)
                result->node_actions[node] += 1 << pop_4_6;
            if (strcmp(token, "64↓6") == 0)
                result->node_actions[node] += 1 << pop_6_4;
            if (strcmp(token, "66↓6") == 0)
                result->node_actions[node] += 1 << pop_6_6;

            token = strtok_r(NULL, delim, &lex);
        }
    }
    // todo: fill node_actions.

    return result;
}

void tn_delete(TunnelNetwork network)
{
    free(network->node_actions);
    free(network);
    return;
}

char *tn_string_of_stack_action(stack_action action)
{
    if (action == transmit_4)
        return ("4→4");
    if (action == transmit_6)
        return ("6→6");
    if (action == push_4_4)
        return ("4↑44");
    if (action == push_4_6)
        return ("4↑46");
    if (action == push_6_4)
        return ("6↑64");
    if (action == push_6_6)
        return ("6↑66");
    if (action == pop_4_4)
        return ("44↓4");
    if (action == pop_4_6)
        return ("46↓4");
    if (action == pop_6_4)
        return ("64↓6");
    if (action == pop_6_6)
        return ("66↓6");
    return "";
}

void tn_print(TunnelNetwork network)
{
    graph_print(network->graph);
    printf("\nTunnel Network properties:\n\n");
    printf("Initial : %s\n", tn_get_node_name(network, network->initial));
    printf("Final : %s\n", tn_get_node_name(network, network->final));
    int num_nodes = tn_get_num_nodes(network);
    for (int node = 0; node < num_nodes; node++)
    {
        printf("node %s :", tn_get_node_name(network, node));
        for (stack_action act = 0; act < NumActions; act++)
            if (tn_node_has_action(network, node, act))
            {
                printf(" %s", tn_string_of_stack_action(act));
            }
        printf("\n");
    }
    return;
}

int tn_get_num_nodes(TunnelNetwork network)
{
    return graph_num_nodes(network->graph);
}

int tn_get_num_edges(TunnelNetwork network)
{
    return graph_num_edges(network->graph);
}

bool tn_is_edge(TunnelNetwork network, int source, int target)
{
    return graph_is_edge(network->graph, source, target);
}

char *tn_get_node_name(TunnelNetwork network, int node)
{
    return graph_get_node_name(network->graph, node);
}

bool tn_node_has_action(TunnelNetwork network, int node, stack_action action)
{
    return (((1 << action) & network->node_actions[node]) != 0);
}

int tn_get_initial(TunnelNetwork network)
{
    return network->initial;
}

void tn_set_initial(TunnelNetwork network, int initial)
{
    network->initial = initial;
}

int tn_get_final(TunnelNetwork network)
{
    return network->final;
}

void tn_set_final(TunnelNetwork network, int final)
{
    network->final = final;
}

char *tn_get_name(TunnelNetwork network)
{
    return graph_get_name(network->graph);
}

void tn_print_path(TunnelNetwork network, tn_step *path, int size_path)
{
    for (int i = 0; i < size_path; i++)
    {
        printf("%s -(%s)-> ", tn_get_node_name(network, path[i].source), tn_string_of_stack_action(path[i].action));
    }
    printf("%s", tn_get_node_name(network, path[size_path - 1].target));
    printf("\n");
    return;
}

void tn_create_dot(TunnelNetwork network, tn_step *path, int size_path, char *name)
{

    FILE *file;

    struct stat st = {0};
    if (stat("./sol", &st) == -1)
        mkdir("./sol", 0777);

    if (name == NULL)
    {
        char nameFile[30];
        snprintf(nameFile, 30, "sol/result.dot");
        file = fopen(nameFile, "w");
        fprintf(file, "digraph Sol{\n");
    }
    else
    {
        int length = strlen(name) + 12;
        char nameFile[length];
        snprintf(nameFile, length, "sol/%s.dot", name);
        file = fopen(nameFile, "w");
        fprintf(file, "digraph %s{\n", name);
    }

    digraph_fill_dot_content(network->graph, file);

    for (int i = 0; i < size_path; i++)
    {
        fprintf(file, "%s -> %s[color=red,fontcolor=red,label=\"%s\"];\n", tn_get_node_name(network, path[i].source), tn_get_node_name(network, path[i].target), tn_string_of_stack_action(path[i].action));
    }

    fprintf(file, "\n}\n");
    fclose(file);
}

tn_step tn_step_create(stack_action action, int source, int target)
{
    tn_step result;
    result.action = action;
    result.source = source;
    result.target = target;
    return result;
}

tn_step tn_step_empty()
{
    return tn_step_create(transmit_4, 0, 0);
}