/* Redistribution Handler
 * Copyright (C) 1998 Kunihiro Ishiguro
 *
 * This file is part of GNU Zebra.
 *
 * GNU Zebra is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation; either version 2, or (at your option) any
 * later version.
 *
 * GNU Zebra is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with GNU Zebra; see the file COPYING.  If not, write to the Free
 * Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
 * 02111-1307, USA.  
 */

#include <zebra.h>

#include "vector.h"
#include "vty.h"
#include "command.h"
#include "prefix.h"
#include "table.h"
#include "stream.h"
#include "zclient.h"
#include "linklist.h"
#include "log.h"

#include "zebra/rib.h"
#include "zebra/zserv.h"
#include "zebra/redistribute.h"
#include "zebra/debug.h"
#include "zebra/router-id.h"

/* master zebra server structure */
extern struct zebra_t zebrad;

int
zebra_check_addr (struct prefix *p)
{
  if (p->family == AF_INET)
    {
      u_int32_t addr;

      addr = p->u.prefix4.s_addr;
      addr = ntohl (addr);

      if (IPV4_NET127 (addr)
          || IN_CLASSD (addr)
          || IPV4_LINKLOCAL(addr))
	return 0;
    }
#ifdef HAVE_IPV6
  if (p->family == AF_INET6)
    {
      if (IN6_IS_ADDR_LOOPBACK (&p->u.prefix6))
	return 0;
      if (IN6_IS_ADDR_LINKLOCAL(&p->u.prefix6))
	return 0;
    }
#endif /* HAVE_IPV6 */
  return 1;
}

static int
is_default (struct prefix *p)
{
  if (p->family == AF_INET)
    if (p->u.prefix4.s_addr == 0 && p->prefixlen == 0)
      return 1;
#ifdef HAVE_IPV6
#if 0  /* IPv6 default separation is now pending until protocol daemon
          can handle that. */
  if (p->family == AF_INET6)
    if (IN6_IS_ADDR_UNSPECIFIED (&p->u.prefix6) && p->prefixlen == 0)
      return 1;
#endif /* 0 */
#endif /* HAVE_IPV6 */
  return 0;
}

static void
zebra_redistribute_default (struct zserv *client)
{
  struct prefix_ipv4 p;
  struct route_table *table;
  struct route_node *rn;
  struct rib *newrib;
#ifdef HAVE_IPV6
  struct prefix_ipv6 p6;
#endif /* HAVE_IPV6 */


  /* Lookup default route. */
  memset (&p, 0, sizeof (struct prefix_ipv4));
  p.family = AF_INET;

  /* Lookup table.  */
  table = vrf_table (AFI_IP, SAFI_UNICAST, 0);
  if (table)
    {
      rn = route_node_lookup (table, (struct prefix *)&p);
      if (rn)
	{
	  for (newrib = rn->info; newrib; newrib = newrib->next)
	    if (CHECK_FLAG (newrib->flags, ZEBRA_FLAG_SELECTED)
		&& newrib->distance != DISTANCE_INFINITY)
	      zsend_route_multipath (ZEBRA_IPV4_ROUTE_ADD, client, &rn->p, newrib);
	  route_unlock_node (rn);
	}
    }

#ifdef HAVE_IPV6
  /* Lookup default route. */
  memset (&p6, 0, sizeof (struct prefix_ipv6));
  p6.family = AF_INET6;

  /* Lookup table.  */
  table = vrf_table (AFI_IP6, SAFI_UNICAST, 0);
  if (table)
    {
      rn = route_node_lookup (table, (struct prefix *)&p6);
      if (rn)
	{
	  for (newrib = rn->info; newrib; newrib = newrib->next)
	    if (CHECK_FLAG (newrib->flags, ZEBRA_FLAG_SELECTED)
		&& newrib->distance != DISTANCE_INFINITY)
	      zsend_route_multipath (ZEBRA_IPV6_ROUTE_ADD, client, &rn->p, newrib);
	  route_unlock_node (rn);
	}
    }
#endif /* HAVE_IPV6 */
}

/* Redistribute routes. */
static void
zebra_redistribute (struct zserv *client, int type)
{
  struct rib *newrib;
  struct route_table *table;
  struct route_node *rn;

  table = vrf_table (AFI_IP, SAFI_UNICAST, 0);
  if (table)
    for (rn = route_top (table); rn; rn = route_next (rn))
    {
      zlog_debug("in func zebra_redistribute,rn->p=%x/%d",rn->p.u.prefix4.s_addr,rn->p.prefixlen);
      for (newrib = rn->info; newrib; newrib = newrib->next)
      {
        zlog_debug("in func zebra_redistribute,newrib->type=%d",newrib->type);
        if (CHECK_FLAG (newrib->flags, ZEBRA_FLAG_SELECTED) 
            && newrib->type == type 
            && newrib->distance != DISTANCE_INFINITY
            && zebra_check_addr (&rn->p))
          {
            zlog_debug("in func zebra_redistribute,zsend_route_multipath: rn->p=%x/%d",rn->p.u.prefix4.s_addr,rn->p.prefixlen);
	          zsend_route_multipath (ZEBRA_IPV4_ROUTE_ADD, client, &rn->p, newrib);
          }
      }
    }
  
#ifdef HAVE_IPV6
  table = vrf_table (AFI_IP6, SAFI_UNICAST, 0);
  if (table)
    for (rn = route_top (table); rn; rn = route_next (rn))
      for (newrib = rn->info; newrib; newrib = newrib->next)
	if (CHECK_FLAG (newrib->flags, ZEBRA_FLAG_SELECTED)
	    && newrib->type == type 
	    && newrib->distance != DISTANCE_INFINITY
	    && zebra_check_addr (&rn->p))
	  zsend_route_multipath (ZEBRA_IPV6_ROUTE_ADD, client, &rn->p, newrib);
#endif /* HAVE_IPV6 */
}

void
redistribute_add (struct prefix *p, struct rib *rib)
{
  struct listnode *node, *nnode;
  struct zserv *client;

  for (ALL_LIST_ELEMENTS (zebrad.client_list, node, nnode, client))
    {
      if (is_default (p))
        {
          if (client->redist_default || client->redist[rib->type])
            {
              if (p->family == AF_INET)
                zsend_route_multipath (ZEBRA_IPV4_ROUTE_ADD, client, p, rib);
#ifdef HAVE_IPV6
              if (p->family == AF_INET6)
                zsend_route_multipath (ZEBRA_IPV6_ROUTE_ADD, client, p, rib);
#endif /* HAVE_IPV6 */	  
	    }
        }
      else if (client->redist[rib->type])
        {
          if (p->family == AF_INET)
            zsend_route_multipath (ZEBRA_IPV4_ROUTE_ADD, client, p, rib);
#ifdef HAVE_IPV6
          if (p->family == AF_INET6)
            zsend_route_multipath (ZEBRA_IPV6_ROUTE_ADD, client, p, rib);
#endif /* HAVE_IPV6 */	  
        }
    }
}

void
redistribute_delete (struct prefix *p, struct rib *rib)
{
  struct listnode *node, *nnode;
  struct zserv *client;

  /* Add DISTANCE_INFINITY check. */
  if (rib->distance == DISTANCE_INFINITY)
    return;

  for (ALL_LIST_ELEMENTS (zebrad.client_list, node, nnode, client))
    {
      if (is_default (p))
	{
	  if (client->redist_default || client->redist[rib->type])
	    {
	      if (p->family == AF_INET)
		zsend_route_multipath (ZEBRA_IPV4_ROUTE_DELETE, client, p,
				       rib);
#ifdef HAVE_IPV6
	      if (p->family == AF_INET6)
		zsend_route_multipath (ZEBRA_IPV6_ROUTE_DELETE, client, p,
				       rib);
#endif /* HAVE_IPV6 */
	    }
	}
      else if (client->redist[rib->type])
	{
	  if (p->family == AF_INET)
	    zsend_route_multipath (ZEBRA_IPV4_ROUTE_DELETE, client, p, rib);
#ifdef HAVE_IPV6
	  if (p->family == AF_INET6)
	    zsend_route_multipath (ZEBRA_IPV6_ROUTE_DELETE, client, p, rib);
#endif /* HAVE_IPV6 */
	}
    }
}

void
zebra_redistribute_add (int command, struct zserv *client, int length)
{
  int type;

  type = stream_getc (client->ibuf);

  if (type == 0 || type >= ZEBRA_ROUTE_MAX)
    return;

  if (! client->redist[type])
    {
      client->redist[type] = 1;
      zebra_redistribute (client, type);
    }
}

void
zebra_redistribute_delete (int command, struct zserv *client, int length)
{
  int type;

  type = stream_getc (client->ibuf);

  if (type == 0 || type >= ZEBRA_ROUTE_MAX)
    return;

  client->redist[type] = 0;
}

void
zebra_redistribute_default_add (int command, struct zserv *client, int length)
{
  client->redist_default = 1;
  zebra_redistribute_default (client);
}     

void
zebra_redistribute_default_delete (int command, struct zserv *client,
				   int length)
{
  client->redist_default = 0;;
}     

/* Interface up information. */
void
zebra_interface_up_update (struct interface *ifp)
{
  struct listnode *node, *nnode;
  struct zserv *client;

  if (IS_ZEBRA_DEBUG_EVENT)
    zlog_debug ("MESSAGE: ZEBRA_INTERFACE_UP %s", ifp->name);

  for (ALL_LIST_ELEMENTS (zebrad.client_list, node, nnode, client))
    zsend_interface_update (ZEBRA_INTERFACE_UP, client, ifp);
}

/* Interface down information. */
void
zebra_interface_down_update (struct interface *ifp)
{
  struct listnode *node, *nnode;
  struct zserv *client;

  if (IS_ZEBRA_DEBUG_EVENT)
    zlog_debug ("MESSAGE: ZEBRA_INTERFACE_DOWN %s", ifp->name);

  for (ALL_LIST_ELEMENTS (zebrad.client_list, node, nnode, client))
    zsend_interface_update (ZEBRA_INTERFACE_DOWN, client, ifp);
}

/* Interface information update. */
void
zebra_interface_add_update (struct interface *ifp)
{
  struct listnode *node, *nnode;
  struct zserv *client;

  if (IS_ZEBRA_DEBUG_EVENT)
    zlog_debug ("MESSAGE: ZEBRA_INTERFACE_ADD %s", ifp->name);
    
  for (ALL_LIST_ELEMENTS (zebrad.client_list, node, nnode, client))
    if (client->ifinfo)
      zsend_interface_add (client, ifp);
}

void
zebra_interface_delete_update (struct interface *ifp)
{
  struct listnode *node, *nnode;
  struct zserv *client;

  if (IS_ZEBRA_DEBUG_EVENT)
    zlog_debug ("MESSAGE: ZEBRA_INTERFACE_DELETE %s", ifp->name);

  for (ALL_LIST_ELEMENTS (zebrad.client_list, node, nnode, client))
    if (client->ifinfo)
      zsend_interface_delete (client, ifp);
}

/* Interface address addition. */
void
zebra_interface_address_add_update (struct interface *ifp,
				    struct connected *ifc)
{
  struct listnode *node, *nnode;
  struct zserv *client;
  struct prefix *p;

  if (IS_ZEBRA_DEBUG_EVENT)
    {
      char buf[INET6_ADDRSTRLEN];

      p = ifc->address;
      zlog_debug ("MESSAGE: ZEBRA_INTERFACE_ADDRESS_ADD %s/%d on %s",
		  inet_ntop (p->family, &p->u.prefix, buf, INET6_ADDRSTRLEN),
		  p->prefixlen, ifc->ifp->name);
    }

  router_id_add_address(ifc);

  for (ALL_LIST_ELEMENTS (zebrad.client_list, node, nnode, client))
    if (client->ifinfo && CHECK_FLAG (ifc->conf, ZEBRA_IFC_REAL))
      zsend_interface_address (ZEBRA_INTERFACE_ADDRESS_ADD, client, ifp, ifc);
}

/* Interface address deletion. */
void
zebra_interface_address_delete_update (struct interface *ifp,
				       struct connected *ifc)
{
  struct listnode *node, *nnode;
  struct zserv *client;
  struct prefix *p;

  if (IS_ZEBRA_DEBUG_EVENT)
    {
      char buf[INET6_ADDRSTRLEN];

      p = ifc->address;
      zlog_debug ("MESSAGE: ZEBRA_INTERFACE_ADDRESS_DELETE %s/%d on %s",
		  inet_ntop (p->family, &p->u.prefix, buf, INET6_ADDRSTRLEN),
		 p->prefixlen, ifc->ifp->name);
    }

  router_id_del_address(ifc);

  for (ALL_LIST_ELEMENTS (zebrad.client_list, node, nnode, client))
    if (client->ifinfo && CHECK_FLAG (ifc->conf, ZEBRA_IFC_REAL))
      zsend_interface_address (ZEBRA_INTERFACE_ADDRESS_DELETE, client, ifp, ifc);
}
