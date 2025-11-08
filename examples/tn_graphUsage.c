#include <stdio.h>
#include <Graph.h>
#include <Parsing.h>
#include <TunnelNetwork.h>

void usage()
{
    printf("Usage: graphParser file\n");
    printf(" Displays information on the graph discribed by file, seen as a network. It should be provided with a .dot file\n");
}

int main(int argc, char *argv[])
{

    if (argc < 2)
    {
        usage();
        return 0;
    }

    Graph graph;
    graph = get_graph_from_file(argv[1]);

    TunnelNetwork network = tn_initialize(graph);

    tn_print(network);

    printf("The network has %d nodes\n", tn_get_num_nodes(network));

    printf("The network has %d edges\n", tn_get_num_edges(network));

    printf("Initial node is %s\n", tn_get_node_name(network, tn_get_initial(network)));

    printf("Final node is %s\n", tn_get_node_name(network, tn_get_final(network)));

    printf("There is ");
    if (!tn_is_edge(network, 0, 1))
        printf("no ");
    printf("edge between nodes %s and %s\n", tn_get_node_name(network, 0), tn_get_node_name(network, 1));

    printf("Node %s has the following actions :", tn_get_node_name(network, 1));
    for (stack_action action = 0; action < NumActions; action++)
    {
        if (tn_node_has_action(network, 1, action))
            printf("%s, ", tn_string_of_stack_action(action));
    }
    printf("\n");

    tn_delete(network);

    graph_delete(graph);
    printf("Graph successfully deleted.\n");
    return 0;
}