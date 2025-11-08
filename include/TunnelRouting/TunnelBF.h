/**
 * @file TunnelBF.h
 * @author Vincent Penelle
 * @brief File to implement a brute force algorithm for the Tunnel Network Routing problem.
 * @version 1
 * @date 2025-10-16
 *
 * @copyright Creative Commons
 *
 */

#ifndef TUNNEL_BF_H
#define TUNNEL_BF_H

#include "TunnelNetwork.h"

/**
 * @brief Brute force that decides if there is a valid simple path of length at most @p length in @p network. If there is such a path, it will be present in @p path after the call, otherwise, path is not modified.
 *
 * @param network The network.
 * @param length The max length of the path sought
 * @param path Array to return a path if one is found.
 * @return int The length of the path found. Returns 0 if no path has been found.
 * @pre @p path must be an array of size at least @p length.
 * @pre @p network must be an initialized TunnelNetwork.
 * @post @p path contains the path found from cell 0 to returned value -1.
 */
int tn_brute_force(TunnelNetwork network, int length, tn_step *path);

#endif