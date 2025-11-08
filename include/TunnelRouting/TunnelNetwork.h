/**
 * @file TunnelNetwork.h
 * @author Vincent Penelle (vincent.penelle@u-bordeaux.fr)
 * @brief Structure to represent a network with IPV4-IPV6 links
 * @version 0.1
 * @date 2025-10-02
 *
 * @copyright Creative Commons
 *
 */

#ifndef COCA_TUNNEL_NETWORK_H
#define COCA_TUNNEL_NETWORK_H

#include "Graph.h"

/**
 * @brief The struct containing the network (an oriented graph, whose nodes can perform stack action, with initial and final nodes of the problem).
 *
 */
typedef struct TunnelNetwork_s *TunnelNetwork;

/**
 * @brief Possible actions that a node can perform on a package.
 *
 */
typedef enum
{
    transmit_4, //< →4
    transmit_6, //< →6
    push_4_4,   //< ↑_4^4
    push_4_6,   //< ↑_4^6
    push_6_4,   //< ↑_6^4
    push_6_6,   //< ↑_6^6
    pop_4_4,    //< ↓_4^4
    pop_4_6,    //< ↓_4^6
    pop_6_4,    //< ↓_6^4
    pop_6_6     //< ↓_6^6
} stack_action;

/**
 * @brief Number of stack actions.
 * 
 */
#define NumActions 10

/**
 * @brief Structure to store a step of an execution path over a tunnel network.
 *
 */
typedef struct tn_step
{
    int source;          ///< The node number source of this step.
    int target;          ///< The node number target of this step.
    stack_action action; ///< The action code of this step.
} tn_step;

/**
 * @brief Initializes a Tunnel Network from a Graph for use in the project. Parses node parameters to determine which are initial, final, and their actions.
 * The graph is NOT copied (it is not supposed to be modified).
 * TODO: format of parsed parameters
 *
 * @param graph The Graph that is the input of the problem.
 * @return TunnelNetwork The structure TunnelNetwork described above.
 */
TunnelNetwork tn_initialize(Graph graph);

/**
 * @brief Deallocates memory used by @p network. Does NOT deallocates the graph.
 *
 * @param network
 */
void tn_delete(TunnelNetwork network);

/**
 * @brief Gets the textual representation of @p action.
 *
 * @param action
 */
char *tn_string_of_stack_action(stack_action action);

/**
 * @brief Printer function to display information about @p network.
 *
 * @param network
 */
void tn_print(TunnelNetwork network);

/**
 * @brief Returns the number of nodes of @p network.
 *
 * @param network
 * @return int
 */
int tn_get_num_nodes(TunnelNetwork network);

/**
 * @brief Returns the number of edges of @p network
 *
 * @param network
 * @return int
 */
int tn_get_num_edges(TunnelNetwork network);

/**
 * @brief Returns true if (@p source, @p target) is an edge in @p network.
 *
 * @pre @p source and @p target must be between 0 and tn_get_num_nodes(@p network).
 * @param network
 * @param source
 * @param target
 * @return true
 * @return false
 */
bool tn_is_edge(TunnelNetwork network, int source, int target);

/**
 * @brief Returns the name of @p node in @p network.
 *
 * @pre @p node must be between 0 and tn_get_num_nodes(@p network)
 * @param network
 * @param node
 * @return char*
 */
char *tn_get_node_name(TunnelNetwork network, int node);

/**
 * @brief Returns true iff the node @p node can perform action @p action.
 *
 * @pre @p node must be between 0 and tn_get_num_nodes(@p network)-1.
 * @pre @p action must be a valid action.
 * @param network
 * @param node
 * @param action
 * @return bool
 */
bool tn_node_has_action(TunnelNetwork network, int node, stack_action action);

/**
 * @brief Gets the initial node of @p network.
 *
 * @param network
 * @return int
 */
int tn_get_initial(TunnelNetwork network);

/**
 * @brief Set the initial node of @p network as @p initial.
 *
 * @param network
 * @param initial
 * @pre @p initial must be between 0 and tn_get_num_nodes(@p network)-1.
 */
void tn_set_initial(TunnelNetwork network, int initial);

/**
 * @brief Gets the final node of @p network.
 *
 * @param network
 * @return int
 */
int tn_get_final(TunnelNetwork network);

/**
 * @brief Sets the final node of @p network as @p final.
 *
 * @param network
 * @param final
 * @pre @p final must be between 0 and tn_get_num_nodes(@p network)-1.
 */
void tn_set_final(TunnelNetwork network, int final);

/**
 * @brief Gets the name of the network
 *
 * @param network
 * @return int
 */
char *tn_get_name(TunnelNetwork network);

/**
 * @brief Prints the path @p path.
 *
 * @param network
 * @param path
 * @param size_path
 */
void tn_print_path(TunnelNetwork network, tn_step *path, int size_path);

/**
 * @brief Generates a dot file representing the path described by @p path (in red) over network @p network. The file will have name <@p name>.dot
 *
 * @param network
 * @param path
 * @param size_path
 * @param name
 */
void tn_create_dot(TunnelNetwork network, tn_step *path, int size_path, char *name);

/**
 * @brief Creates a tn_step with values given in argument.
 *
 * @param action
 * @param source
 * @param target
 * @return tn_step
 */
tn_step tn_step_create(stack_action action, int source, int target);

/**
 * @brief Creates a dummy step.
 *
 * @return tn_step
 */
tn_step tn_step_empty();

#endif