/* OSPF VTY interface.
 * Copyright (C) 2005 6WIND <alain.ritoux@6wind.com>
 * Copyright (C) 2000 Toshiaki Takada
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

#include "memory.h"
#include "thread.h"
#include "prefix.h"
#include "table.h"
#include "vty.h"
#include "command.h"
#include "plist.h"
#include "log.h"
#include "zclient.h"

#include "ospfd/ospfd.h"
#include "ospfd/ospf_asbr.h"
#include "ospfd/ospf_lsa.h"
#include "ospfd/ospf_lsdb.h"
#include "ospfd/ospf_ism.h"
#include "ospfd/ospf_interface.h"
#include "ospfd/ospf_nsm.h"
#include "ospfd/ospf_neighbor.h"
#include "ospfd/ospf_flood.h"
#include "ospfd/ospf_abr.h"
#include "ospfd/ospf_spf.h"
#include "ospfd/ospf_route.h"
#include "ospfd/ospf_zebra.h"
/*#include "ospfd/ospf_routemap.h" */
#include "ospfd/ospf_vty.h"
#include "ospfd/ospf_dump.h"

int global_phase;
int phase_all;
void fileToMatrix_str(const char *path,DATA_INFO_STR *data_info){

    FILE *file=NULL;
    //char c;
    zlog_debug("in func fileToMatrix_str,%s",path);
    file=fopen(path,"r");

    if(file==NULL){
      zlog_debug("open file fail");
      return;
    }

    //zlog_debug("open success!");

    char str[200];
    int row_total=0;
    while(fgets(str,200,file)!=NULL){
        //zlog_debug("get line");
        row_total++;
    }

    zlog_debug("%d\n",row_total);

    //record row count, then  count data in each line, record in line_total array
    data_info->row_total=row_total;
    data_info->line_total=(int *)malloc(sizeof(int)*row_total);
    data_info->matrix=(char ***)malloc(sizeof(char**)*row_total);
    rewind(file);

    char *token;
    int line_total,line_pos;
    int row_pos=0;


    while(fgets(str,200,file)!=NULL){
        //get number count in each line
        line_total=0;
        token=strtok(str,",");
        while(token!=NULL){
            if(token[0]!='\r'&&token[0]!='\n')
                line_total++;
            zlog_debug("%s",token);
            token=strtok(NULL,",");
        }
        //zlog_debug("line_total=%d",line_total);
        data_info->line_total[row_pos]=line_total;
        data_info->matrix[row_pos]=(char **)malloc(line_total*sizeof(char *));
        row_pos++;
    }   


    rewind(file);
    row_pos=0;
    while(fgets(str,200,file)!=NULL){
        //store each number to matrix
        line_pos=0;
        //zlog_debug("str=%s",str);
        token=strtok(str,",");
        while(token!=NULL){
            if(token[0]!='\r'&&token[0]!='\n'){
                
                for(unsigned int k=0;k<strlen(token);++k){
                    if(token[k]=='\r' || token[k]=='\n'){
                        //zlog_debug("k=%d,there is a \\n",k);
                        token[k]='\0';
                    }
                }
                //zlog_debug("token=%s,strlen=%d,",token,strlen(token));
                data_info->matrix[row_pos][line_pos]=(char *)malloc(strlen(token)+1);


                strcpy(data_info->matrix[row_pos][line_pos],token);
                line_pos++;
            }
            token=strtok(NULL,",");
        }

        row_pos++;
    } 
    zlog_debug("finish func fileToMatrix_str");
    fclose(file);

}

static const char *ospf_network_type_str[] =
{
  "Null",
  "POINTOPOINT",
  "BROADCAST",
  "NBMA",
  "POINTOMULTIPOINT",
  "VIRTUALLINK",
  "LOOPBACK"
};


/* Utility functions. */
static int
ospf_str2area_id (const char *str, struct in_addr *area_id, int *format)
{
  char *endptr = NULL;
  unsigned long ret;

  /* match "A.B.C.D". */
  if (strchr (str, '.') != NULL)
    {
      ret = inet_aton (str, area_id);
      if (!ret)
        return -1;
      *format = OSPF_AREA_ID_FORMAT_ADDRESS;
    }
  /* match "<0-4294967295>". */
  else
    {
      if (*str == '-')
        return -1;
      errno = 0;
      ret = strtoul (str, &endptr, 10);
      if (*endptr != '\0' || errno || ret > UINT32_MAX)
        return -1;

      area_id->s_addr = htonl (ret);
      *format = OSPF_AREA_ID_FORMAT_DECIMAL;
    }

  return 0;
}


static int
str2metric (const char *str, int *metric)
{
  /* Sanity check. */
  if (str == NULL)
    return 0;

  *metric = strtol (str, NULL, 10);
  if (*metric < 0 && *metric > 16777214)
    {
      /* vty_out (vty, "OSPF metric value is invalid%s", VTY_NEWLINE); */
      return 0;
    }

  return 1;
}

static int
str2metric_type (const char *str, int *metric_type)
{
  /* Sanity check. */
  if (str == NULL)
    return 0;

  if (strncmp (str, "1", 1) == 0)
    *metric_type = EXTERNAL_METRIC_TYPE_1;
  else if (strncmp (str, "2", 1) == 0)
    *metric_type = EXTERNAL_METRIC_TYPE_2;
  else
    return 0;

  return 1;
}

int
ospf_oi_count (struct interface *ifp)
{
  struct route_node *rn;
  int i = 0;

  for (rn = route_top (IF_OIFS (ifp)); rn; rn = route_next (rn))
    if (rn->info)
      i++;

  return i;
}


DEFUN (router_ospf,
       router_ospf_cmd,
       "router ospf",
       "Enable a routing process\n"
       "Start OSPF configuration\n")
{
  vty->node = OSPF_NODE;
  vty->index = ospf_get ();
 
  return CMD_SUCCESS;
}

DEFUN (no_router_ospf,
       no_router_ospf_cmd,
       "no router ospf",
       NO_STR
       "Enable a routing process\n"
       "Start OSPF configuration\n")
{
  struct ospf *ospf;

  ospf = ospf_lookup ();
  if (ospf == NULL)
    {
      vty_out (vty, "There isn't active ospf instance%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  ospf_finish (ospf);

  return CMD_SUCCESS;
}

DEFUN (ospf_router_id,
       ospf_router_id_cmd,
       "ospf router-id A.B.C.D",
       "OSPF specific commands\n"
       "router-id for the OSPF process\n"
       "OSPF router-id in IP address format\n")
{
  struct ospf *ospf = vty->index;
  struct in_addr router_id;
  int ret;

  ret = inet_aton (argv[0], &router_id);
  if (!ret)
    {
      vty_out (vty, "Please specify Router ID by A.B.C.D%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  ospf->router_id_static = router_id;
  
  ospf_router_id_update (ospf);
  
  return CMD_SUCCESS;
}

ALIAS (ospf_router_id,
       router_ospf_id_cmd,
       "router-id A.B.C.D",
       "router-id for the OSPF process\n"
       "OSPF router-id in IP address format\n")

DEFUN (no_ospf_router_id,
       no_ospf_router_id_cmd,
       "no ospf router-id",
       NO_STR
       "OSPF specific commands\n"
       "router-id for the OSPF process\n")
{
  struct ospf *ospf = vty->index;

  ospf->router_id_static.s_addr = 0;

  ospf_router_id_update (ospf);

  return CMD_SUCCESS;
}

ALIAS (no_ospf_router_id,
       no_router_ospf_id_cmd,
       "no router-id",
       NO_STR
       "router-id for the OSPF process\n")

static void
ospf_passive_interface_default (struct ospf *ospf, u_char newval)
{
  struct listnode *ln;
  struct interface *ifp;
  struct ospf_interface *oi;
  
  ospf->passive_interface_default = newval;

  for (ALL_LIST_ELEMENTS_RO (om->iflist, ln, ifp))
    {
      if (ifp &&
          OSPF_IF_PARAM_CONFIGURED (IF_DEF_PARAMS (ifp), passive_interface))
        UNSET_IF_PARAM (IF_DEF_PARAMS (ifp), passive_interface);
    }
  for (ALL_LIST_ELEMENTS_RO (ospf->oiflist, ln, oi))
    {
      if (OSPF_IF_PARAM_CONFIGURED (oi->params, passive_interface))
        UNSET_IF_PARAM (oi->params, passive_interface);
      /* update multicast memberships */
      ospf_if_set_multicast(oi);
    }
}

static void
ospf_passive_interface_update (struct ospf *ospf, struct interface *ifp,
                               struct in_addr addr, 
                               struct ospf_if_params *params, u_char value)
{
  u_char dflt;
  
  params->passive_interface = value;
  if (params != IF_DEF_PARAMS (ifp))
    {
      if (OSPF_IF_PARAM_CONFIGURED (IF_DEF_PARAMS (ifp), passive_interface))
        dflt = IF_DEF_PARAMS (ifp)->passive_interface;
      else
        dflt = ospf->passive_interface_default;
      
      if (value != dflt)
        SET_IF_PARAM (params, passive_interface);
      else
        UNSET_IF_PARAM (params, passive_interface);
      
      ospf_free_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }
  else
    {
      if (value != ospf->passive_interface_default)
        SET_IF_PARAM (params, passive_interface);
      else
        UNSET_IF_PARAM (params, passive_interface);
    }
}

DEFUN (ospf_passive_interface,
       ospf_passive_interface_addr_cmd,
       "passive-interface IFNAME A.B.C.D",
       "Suppress routing updates on an interface\n"
       "Interface's name\n")
{
  struct interface *ifp;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
  struct route_node *rn;
  struct ospf *ospf = vty->index;

  if (argc == 0)
    {
      ospf_passive_interface_default (ospf, OSPF_IF_PASSIVE);
      return CMD_SUCCESS;
    }

  ifp = if_get_by_name (argv[0]);

  params = IF_DEF_PARAMS (ifp);

  if (argc == 2)
    {
      ret = inet_aton(argv[1], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_get_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }
  ospf_passive_interface_update (ospf, ifp, addr, params, OSPF_IF_PASSIVE);

  /* XXX We should call ospf_if_set_multicast on exactly those
   * interfaces for which the passive property changed.  It is too much
   * work to determine this set, so we do this for every interface.
   * This is safe and reasonable because ospf_if_set_multicast uses a
   * record of joined groups to avoid systems calls if the desired
   * memberships match the current memership.
   */

  for (rn = route_top(IF_OIFS(ifp)); rn; rn = route_next (rn))
    {
      struct ospf_interface *oi = rn->info;

      if (oi && (OSPF_IF_PARAM(oi, passive_interface) == OSPF_IF_PASSIVE))
	ospf_if_set_multicast(oi);
    }
  /*
   * XXX It is not clear what state transitions the interface needs to
   * undergo when going from active to passive.  Fixing this will
   * require precise identification of interfaces having such a
   * transition.
   */

 return CMD_SUCCESS;
}

ALIAS (ospf_passive_interface,
       ospf_passive_interface_cmd,
       "passive-interface IFNAME",
       "Suppress routing updates on an interface\n"
       "Interface's name\n")

ALIAS (ospf_passive_interface,
       ospf_passive_interface_default_cmd,
       "passive-interface default",
       "Suppress routing updates on an interface\n"
       "Suppress routing updates on interfaces by default\n")

DEFUN (no_ospf_passive_interface,
       no_ospf_passive_interface_addr_cmd,
       "no passive-interface IFNAME A.B.C.D",
       NO_STR
       "Allow routing updates on an interface\n"
       "Interface's name\n")
{
  struct interface *ifp;
  struct in_addr addr;
  struct ospf_if_params *params;
  int ret;
  struct route_node *rn;
  struct ospf *ospf = vty->index;

  if (argc == 0)
    {
      ospf_passive_interface_default (ospf, OSPF_IF_ACTIVE);
      return CMD_SUCCESS;
    }
    
  ifp = if_get_by_name (argv[0]);

  params = IF_DEF_PARAMS (ifp);

  if (argc == 2)
    {
      ret = inet_aton(argv[1], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_lookup_if_params (ifp, addr);
      if (params == NULL)
	return CMD_SUCCESS;
    }
  ospf_passive_interface_update (ospf, ifp, addr, params, OSPF_IF_ACTIVE);

  /* XXX We should call ospf_if_set_multicast on exactly those
   * interfaces for which the passive property changed.  It is too much
   * work to determine this set, so we do this for every interface.
   * This is safe and reasonable because ospf_if_set_multicast uses a
   * record of joined groups to avoid systems calls if the desired
   * memberships match the current memership.
   */
  for (rn = route_top(IF_OIFS(ifp)); rn; rn = route_next (rn))
    {
      struct ospf_interface *oi = rn->info;

      if (oi && (OSPF_IF_PARAM(oi, passive_interface) == OSPF_IF_ACTIVE))
        ospf_if_set_multicast(oi);
    }

  return CMD_SUCCESS;
}

ALIAS (no_ospf_passive_interface,
       no_ospf_passive_interface_cmd,
       "no passive-interface IFNAME",
       NO_STR
       "Allow routing updates on an interface\n"
       "Interface's name\n")

ALIAS (no_ospf_passive_interface,
       no_ospf_passive_interface_default_cmd,
       "no passive-interface default",
       NO_STR
       "Allow routing updates on an interface\n"
       "Allow routing updates on interfaces by default\n")
       
DEFUN (ospf_network_area,
       ospf_network_area_cmd,
       "network A.B.C.D/M area (A.B.C.D|<0-4294967295>)",
       "Enable routing on an IP network\n"
       "OSPF network prefix\n"
       "Set the OSPF area ID\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n")
{
  struct ospf *ospf= vty->index;
  struct prefix_ipv4 p;
  struct in_addr area_id;
  int ret, format;

  /* Get network prefix and Area ID. */
  VTY_GET_IPV4_PREFIX ("network prefix", p, argv[0]);
  VTY_GET_OSPF_AREA_ID (area_id, format, argv[1]);

  ret = ospf_network_set (ospf, &p, area_id);
  if (ret == 0)
    {
      vty_out (vty, "There is already same network statement.%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  return CMD_SUCCESS;
}

DEFUN (no_ospf_network_area,
       no_ospf_network_area_cmd,
       "no network A.B.C.D/M area (A.B.C.D|<0-4294967295>)",
       NO_STR
       "Enable routing on an IP network\n"
       "OSPF network prefix\n"
       "Set the OSPF area ID\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n")
{
  struct ospf *ospf = (struct ospf *) vty->index;
  struct prefix_ipv4 p;
  struct in_addr area_id;
  int ret, format;

  /* Get network prefix and Area ID. */
  VTY_GET_IPV4_PREFIX ("network prefix", p, argv[0]);
  VTY_GET_OSPF_AREA_ID (area_id, format, argv[1]);

  ret = ospf_network_unset (ospf, &p, area_id);
  if (ret == 0)
    {
      vty_out (vty, "Can't find specified network area configuration.%s",
	       VTY_NEWLINE);
      return CMD_WARNING;
    }

  return CMD_SUCCESS;
}


DEFUN (ospf_area_range,
       ospf_area_range_cmd,
       "area (A.B.C.D|<0-4294967295>) range A.B.C.D/M",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Summarize routes matching address/mask (border routers only)\n"
       "Area range prefix\n")
{
  struct ospf *ospf = vty->index;
  struct prefix_ipv4 p;
  struct in_addr area_id;
  int format;
  u_int32_t cost;

  VTY_GET_OSPF_AREA_ID (area_id, format, argv[0]);
  VTY_GET_IPV4_PREFIX ("area range", p, argv[1]);

  ospf_area_range_set (ospf, area_id, &p, OSPF_AREA_RANGE_ADVERTISE);
  if (argc > 2)
    {
      VTY_GET_INTEGER ("range cost", cost, argv[2]);
      ospf_area_range_cost_set (ospf, area_id, &p, cost);
    }
  printf("this is a test\n");
  return CMD_SUCCESS;
}

ALIAS (ospf_area_range,
       ospf_area_range_advertise_cmd,
       "area (A.B.C.D|<0-4294967295>) range A.B.C.D/M advertise",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "OSPF area range for route advertise (default)\n"
       "Area range prefix\n"
       "Advertise this range (default)\n")

ALIAS (ospf_area_range,
       ospf_area_range_cost_cmd,
       "area (A.B.C.D|<0-4294967295>) range A.B.C.D/M cost <0-16777215>",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Summarize routes matching address/mask (border routers only)\n"
       "Area range prefix\n"
       "User specified metric for this range\n"
       "Advertised metric for this range\n")

ALIAS (ospf_area_range,
       ospf_area_range_advertise_cost_cmd,
       "area (A.B.C.D|<0-4294967295>) range A.B.C.D/M advertise cost <0-16777215>",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Summarize routes matching address/mask (border routers only)\n"
       "Area range prefix\n"
       "Advertise this range (default)\n"
       "User specified metric for this range\n"
       "Advertised metric for this range\n")

DEFUN (ospf_area_range_not_advertise,
       ospf_area_range_not_advertise_cmd,
       "area (A.B.C.D|<0-4294967295>) range A.B.C.D/M not-advertise",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Summarize routes matching address/mask (border routers only)\n"
       "Area range prefix\n"
       "DoNotAdvertise this range\n")
{
  struct ospf *ospf = vty->index;
  struct prefix_ipv4 p;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID (area_id, format, argv[0]);
  VTY_GET_IPV4_PREFIX ("area range", p, argv[1]);

  ospf_area_range_set (ospf, area_id, &p, 0);

  return CMD_SUCCESS;
}

DEFUN (no_ospf_area_range,
       no_ospf_area_range_cmd,
       "no area (A.B.C.D|<0-4294967295>) range A.B.C.D/M",
       NO_STR
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Summarize routes matching address/mask (border routers only)\n"
       "Area range prefix\n")
{
  struct ospf *ospf = vty->index;
  struct prefix_ipv4 p;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID (area_id, format, argv[0]);
  VTY_GET_IPV4_PREFIX ("area range", p, argv[1]);

  ospf_area_range_unset (ospf, area_id, &p);

  return CMD_SUCCESS;
}

ALIAS (no_ospf_area_range,
       no_ospf_area_range_advertise_cmd,
       "no area (A.B.C.D|<0-4294967295>) range A.B.C.D/M (advertise|not-advertise)",
       NO_STR
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Summarize routes matching address/mask (border routers only)\n"
       "Area range prefix\n"
       "Advertise this range (default)\n"
       "DoNotAdvertise this range\n")

ALIAS (no_ospf_area_range,
       no_ospf_area_range_cost_cmd,
       "no area (A.B.C.D|<0-4294967295>) range A.B.C.D/M cost <0-16777215>",
       NO_STR
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Summarize routes matching address/mask (border routers only)\n"
       "Area range prefix\n"
       "User specified metric for this range\n"
       "Advertised metric for this range\n")

ALIAS (no_ospf_area_range,
       no_ospf_area_range_advertise_cost_cmd,
       "no area (A.B.C.D|<0-4294967295>) range A.B.C.D/M advertise cost <0-16777215>",
       NO_STR
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Summarize routes matching address/mask (border routers only)\n"
       "Area range prefix\n"
       "Advertise this range (default)\n"
       "User specified metric for this range\n"
       "Advertised metric for this range\n")

DEFUN (ospf_area_range_substitute,
       ospf_area_range_substitute_cmd,
       "area (A.B.C.D|<0-4294967295>) range A.B.C.D/M substitute A.B.C.D/M",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Summarize routes matching address/mask (border routers only)\n"
       "Area range prefix\n"
       "Announce area range as another prefix\n"
       "Network prefix to be announced instead of range\n")
{
  struct ospf *ospf = vty->index;
  struct prefix_ipv4 p, s;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID (area_id, format, argv[0]);
  VTY_GET_IPV4_PREFIX ("area range", p, argv[1]);
  VTY_GET_IPV4_PREFIX ("substituted network prefix", s, argv[2]);

  ospf_area_range_substitute_set (ospf, area_id, &p, &s);

  return CMD_SUCCESS;
}

DEFUN (no_ospf_area_range_substitute,
       no_ospf_area_range_substitute_cmd,
       "no area (A.B.C.D|<0-4294967295>) range A.B.C.D/M substitute A.B.C.D/M",
       NO_STR
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Summarize routes matching address/mask (border routers only)\n"
       "Area range prefix\n"
       "Announce area range as another prefix\n"
       "Network prefix to be announced instead of range\n")
{
  struct ospf *ospf = vty->index;
  struct prefix_ipv4 p, s;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID (area_id, format, argv[0]);
  VTY_GET_IPV4_PREFIX ("area range", p, argv[1]);
  VTY_GET_IPV4_PREFIX ("substituted network prefix", s, argv[2]);

  ospf_area_range_substitute_unset (ospf, area_id, &p);

  return CMD_SUCCESS;
}


/* Command Handler Logic in VLink stuff is delicate!!

	ALTER AT YOUR OWN RISK!!!!

	Various dummy values are used to represent 'NoChange' state for
	VLink configuration NOT being changed by a VLink command, and
	special syntax is used within the command strings so that the
	typed in command verbs can be seen in the configuration command
	bacckend handler.  This is to drastically reduce the verbeage
	required to coe up with a reasonably compatible Cisco VLink command

	- Matthew Grant <grantma@anathoth.gen.nz> 
	Wed, 21 Feb 2001 15:13:52 +1300
 */


/* Configuration data for virtual links 
 */ 
struct ospf_vl_config_data {
  struct vty *vty;		/* vty stuff */
  struct in_addr area_id;	/* area ID from command line */
  int format;			/* command line area ID format */
  struct in_addr vl_peer;	/* command line vl_peer */
  int auth_type;		/* Authehntication type, if given */
  char *auth_key;		/* simple password if present */
  int crypto_key_id;		/* Cryptographic key ID */
  char *md5_key;		/* MD5 authentication key */
  int hello_interval;	        /* Obvious what these are... */
  int retransmit_interval; 
  int transmit_delay;
  int dead_interval;
};

static void
ospf_vl_config_data_init (struct ospf_vl_config_data *vl_config, 
			  struct vty *vty)
{
  memset (vl_config, 0, sizeof (struct ospf_vl_config_data));
  vl_config->auth_type = OSPF_AUTH_CMD_NOTSEEN;
  vl_config->vty = vty;
}

static struct ospf_vl_data *
ospf_find_vl_data (struct ospf *ospf, struct ospf_vl_config_data *vl_config)
{
  struct ospf_area *area;
  struct ospf_vl_data *vl_data;
  struct vty *vty;
  struct in_addr area_id;

  vty = vl_config->vty;
  area_id = vl_config->area_id;

  if (area_id.s_addr == OSPF_AREA_BACKBONE)
    {
      vty_out (vty, 
	       "Configuring VLs over the backbone is not allowed%s",
               VTY_NEWLINE);
      return NULL;
    }
  area = ospf_area_get (ospf, area_id, vl_config->format);

  if (area->external_routing != OSPF_AREA_DEFAULT)
    {
      if (vl_config->format == OSPF_AREA_ID_FORMAT_ADDRESS)
	vty_out (vty, "Area %s is %s%s",
		 inet_ntoa (area_id),
		 area->external_routing == OSPF_AREA_NSSA?"nssa":"stub",
		 VTY_NEWLINE);
      else
	vty_out (vty, "Area %ld is %s%s",
		 (u_long)ntohl (area_id.s_addr),
		 area->external_routing == OSPF_AREA_NSSA?"nssa":"stub",
		 VTY_NEWLINE);	
      return NULL;
    }
  
  if ((vl_data = ospf_vl_lookup (ospf, area, vl_config->vl_peer)) == NULL)
    {
      vl_data = ospf_vl_data_new (area, vl_config->vl_peer);
      if (vl_data->vl_oi == NULL)
	{
	  vl_data->vl_oi = ospf_vl_new (ospf, vl_data);
	  ospf_vl_add (ospf, vl_data);
	  ospf_spf_calculate_schedule (ospf);
	}
    }
  return vl_data;
}


static int
ospf_vl_set_security (struct ospf_vl_data *vl_data,
		      struct ospf_vl_config_data *vl_config)
{
  struct crypt_key *ck;
  struct vty *vty;
  struct interface *ifp = vl_data->vl_oi->ifp;

  vty = vl_config->vty;

  if (vl_config->auth_type != OSPF_AUTH_CMD_NOTSEEN)
    {
      SET_IF_PARAM (IF_DEF_PARAMS (ifp), auth_type);
      IF_DEF_PARAMS (ifp)->auth_type = vl_config->auth_type;
    }

  if (vl_config->auth_key)
    {
      memset(IF_DEF_PARAMS (ifp)->auth_simple, 0, OSPF_AUTH_SIMPLE_SIZE+1);
      strncpy ((char *) IF_DEF_PARAMS (ifp)->auth_simple, vl_config->auth_key, 
	       OSPF_AUTH_SIMPLE_SIZE);
    }
  else if (vl_config->md5_key)
    {
      if (ospf_crypt_key_lookup (IF_DEF_PARAMS (ifp)->auth_crypt, vl_config->crypto_key_id) 
	  != NULL)
	{
	  vty_out (vty, "OSPF: Key %d already exists%s",
		   vl_config->crypto_key_id, VTY_NEWLINE);
	  return CMD_WARNING;
	}
      ck = ospf_crypt_key_new ();
      ck->key_id = vl_config->crypto_key_id;
      memset(ck->auth_key, 0, OSPF_AUTH_MD5_SIZE+1);
      strncpy ((char *) ck->auth_key, vl_config->md5_key, OSPF_AUTH_MD5_SIZE);
      
      ospf_crypt_key_add (IF_DEF_PARAMS (ifp)->auth_crypt, ck);
    }
  else if (vl_config->crypto_key_id != 0)
    {
      /* Delete a key */

      if (ospf_crypt_key_lookup (IF_DEF_PARAMS (ifp)->auth_crypt, 
				 vl_config->crypto_key_id) == NULL)
	{
	  vty_out (vty, "OSPF: Key %d does not exist%s", 
		   vl_config->crypto_key_id, VTY_NEWLINE);
	  return CMD_WARNING;
	}
      
      ospf_crypt_key_delete (IF_DEF_PARAMS (ifp)->auth_crypt, vl_config->crypto_key_id);

    }
  
  return CMD_SUCCESS;
}

static int
ospf_vl_set_timers (struct ospf_vl_data *vl_data,
		    struct ospf_vl_config_data *vl_config)
{
  struct interface *ifp = ifp = vl_data->vl_oi->ifp;
  /* Virtual Link data initialised to defaults, so only set
     if a value given */
  if (vl_config->hello_interval)
    {
      SET_IF_PARAM (IF_DEF_PARAMS (ifp), v_hello);
      IF_DEF_PARAMS (ifp)->v_hello = vl_config->hello_interval;
    }

  if (vl_config->dead_interval)
    {
      SET_IF_PARAM (IF_DEF_PARAMS (ifp), v_wait);
      IF_DEF_PARAMS (ifp)->v_wait = vl_config->dead_interval;
    }

  if (vl_config->retransmit_interval)
    {
      SET_IF_PARAM (IF_DEF_PARAMS (ifp), retransmit_interval);
      IF_DEF_PARAMS (ifp)->retransmit_interval = vl_config->retransmit_interval;
    }
  
  if (vl_config->transmit_delay)
    {
      SET_IF_PARAM (IF_DEF_PARAMS (ifp), transmit_delay);
      IF_DEF_PARAMS (ifp)->transmit_delay = vl_config->transmit_delay;
    }
  
  return CMD_SUCCESS;
}



/* The business end of all of the above */
static int
ospf_vl_set (struct ospf *ospf, struct ospf_vl_config_data *vl_config)
{
  struct ospf_vl_data *vl_data;
  int ret;

  vl_data = ospf_find_vl_data (ospf, vl_config);
  if (!vl_data)
    return CMD_WARNING;
  
  /* Process this one first as it can have a fatal result, which can
     only logically occur if the virtual link exists already
     Thus a command error does not result in a change to the
     running configuration such as unexpectedly altered timer 
     values etc.*/
  ret = ospf_vl_set_security (vl_data, vl_config);
  if (ret != CMD_SUCCESS)
    return ret;

  /* Set any time based parameters, these area already range checked */

  ret = ospf_vl_set_timers (vl_data, vl_config);
  if (ret != CMD_SUCCESS)
    return ret;

  return CMD_SUCCESS;

}

/* This stuff exists to make specifying all the alias commands A LOT simpler
 */
#define VLINK_HELPSTR_IPADDR \
       "OSPF area parameters\n" \
       "OSPF area ID in IP address format\n" \
       "OSPF area ID as a decimal value\n" \
       "Configure a virtual link\n" \
       "Router ID of the remote ABR\n"

#define VLINK_HELPSTR_AUTHTYPE_SIMPLE \
       "Enable authentication on this virtual link\n" \
       "dummy string \n" 

#define VLINK_HELPSTR_AUTHTYPE_ALL \
       VLINK_HELPSTR_AUTHTYPE_SIMPLE \
       "Use null authentication\n" \
       "Use message-digest authentication\n"

#define VLINK_HELPSTR_TIME_PARAM_NOSECS \
       "Time between HELLO packets\n" \
       "Time between retransmitting lost link state advertisements\n" \
       "Link state transmit delay\n" \
       "Interval after which a neighbor is declared dead\n"

#define VLINK_HELPSTR_TIME_PARAM \
       VLINK_HELPSTR_TIME_PARAM_NOSECS \
       "Seconds\n"

#define VLINK_HELPSTR_AUTH_SIMPLE \
       "Authentication password (key)\n" \
       "The OSPF password (key)"

#define VLINK_HELPSTR_AUTH_MD5 \
       "Message digest authentication password (key)\n" \
       "dummy string \n" \
       "Key ID\n" \
       "Use MD5 algorithm\n" \
       "The OSPF password (key)"

DEFUN (ospf_area_vlink,
       ospf_area_vlink_cmd,
       "area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D",
       VLINK_HELPSTR_IPADDR)
{
  struct ospf *ospf = vty->index;
  struct ospf_vl_config_data vl_config;
  char auth_key[OSPF_AUTH_SIMPLE_SIZE+1];
  char md5_key[OSPF_AUTH_MD5_SIZE+1]; 
  int i;
  int ret;
  
  ospf_vl_config_data_init(&vl_config, vty);

  /* Read off first 2 parameters and check them */
  ret = ospf_str2area_id (argv[0], &vl_config.area_id, &vl_config.format);
  if (ret < 0)
    {
      vty_out (vty, "OSPF area ID is invalid%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  ret = inet_aton (argv[1], &vl_config.vl_peer);
  if (! ret)
    {
      vty_out (vty, "Please specify valid Router ID as a.b.c.d%s",
               VTY_NEWLINE);
      return CMD_WARNING;
    }

  if (argc <=2)
    {
      /* Thats all folks! - BUGS B. strikes again!!!*/

      return  ospf_vl_set (ospf, &vl_config);
    }

  /* Deal with other parameters */
  for (i=2; i < argc; i++)
    {

      /* vty_out (vty, "argv[%d] - %s%s", i, argv[i], VTY_NEWLINE); */

      switch (argv[i][0])
	{

	case 'a':
	  if (i > 2 || strncmp (argv[i], "authentication-", 15) == 0)
	    {
	      /* authentication-key - this option can occur anywhere on 
		                      command line.  At start of command line
				      must check for authentication option. */
	      memset (auth_key, 0, OSPF_AUTH_SIMPLE_SIZE + 1);
	      strncpy (auth_key, argv[i+1], OSPF_AUTH_SIMPLE_SIZE);
	      vl_config.auth_key = auth_key;
	      i++;
	    }
	  else if (strncmp (argv[i], "authentication", 14) == 0)
	    {
	      /* authentication  - this option can only occur at start
		                   of command line */
	      vl_config.auth_type = OSPF_AUTH_SIMPLE;
	      if ((i+1) < argc)
		{
		  if (strncmp (argv[i+1], "n", 1) == 0)
		    {
		      /* "authentication null" */
		      vl_config.auth_type = OSPF_AUTH_NULL;
		      i++;
		    }
		  else if (strncmp (argv[i+1], "m", 1) == 0
			   && strcmp (argv[i+1], "message-digest-") != 0)
		    {
		      /* "authentication message-digest" */ 
		      vl_config.auth_type = OSPF_AUTH_CRYPTOGRAPHIC;
		      i++;
		    }
		}
	    }
	  break;

	case 'm':
	  /* message-digest-key */
	  i++;
	  vl_config.crypto_key_id = strtol (argv[i], NULL, 10);
	  if (vl_config.crypto_key_id < 0)
	    return CMD_WARNING;
	  i++;
	  memset(md5_key, 0, OSPF_AUTH_MD5_SIZE+1);
	  strncpy (md5_key, argv[i], OSPF_AUTH_MD5_SIZE);
	  vl_config.md5_key = md5_key; 
	  break;

	case 'h':
	  /* Hello interval */
	  i++;
	  vl_config.hello_interval = strtol (argv[i], NULL, 10);
	  if (vl_config.hello_interval < 0) 
	    return CMD_WARNING;
	  break;

	case 'r':
	  /* Retransmit Interval */
	  i++;
	  vl_config.retransmit_interval = strtol (argv[i], NULL, 10);
	  if (vl_config.retransmit_interval < 0)
	    return CMD_WARNING;
	  break;

	case 't':
	  /* Transmit Delay */
	  i++;
	  vl_config.transmit_delay = strtol (argv[i], NULL, 10);
	  if (vl_config.transmit_delay < 0)
	    return CMD_WARNING;
	  break;

	case 'd':
	  /* Dead Interval */
	  i++;
	  vl_config.dead_interval = strtol (argv[i], NULL, 10);
	  if (vl_config.dead_interval < 0)
	    return CMD_WARNING;
	  break;
	}
    }


  /* Action configuration */

  return ospf_vl_set (ospf, &vl_config);

}

DEFUN (no_ospf_area_vlink,
       no_ospf_area_vlink_cmd,
       "no area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D",
       NO_STR
       VLINK_HELPSTR_IPADDR)
{
  struct ospf *ospf = vty->index;
  struct ospf_area *area;
  struct ospf_vl_config_data vl_config;
  struct ospf_vl_data *vl_data = NULL;
  char auth_key[OSPF_AUTH_SIMPLE_SIZE+1];
  int i;
  int ret, format;

  ospf_vl_config_data_init(&vl_config, vty);

  ret = ospf_str2area_id (argv[0], &vl_config.area_id, &format);
  if (ret < 0)
    {
      vty_out (vty, "OSPF area ID is invalid%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  area = ospf_area_lookup_by_area_id (ospf, vl_config.area_id);
  if (!area)
    {
      vty_out (vty, "Area does not exist%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  ret = inet_aton (argv[1], &vl_config.vl_peer);
  if (! ret)
    {
      vty_out (vty, "Please specify valid Router ID as a.b.c.d%s",
               VTY_NEWLINE);
      return CMD_WARNING;
    }

  if (argc <=2)
    {
      /* Basic VLink no command */
      /* Thats all folks! - BUGS B. strikes again!!!*/
      if ((vl_data = ospf_vl_lookup (ospf, area, vl_config.vl_peer)))
	ospf_vl_delete (ospf, vl_data);

      ospf_area_check_free (ospf, vl_config.area_id);
      
      return CMD_SUCCESS;
    }

  /* If we are down here, we are reseting parameters */

  /* Deal with other parameters */
  for (i=2; i < argc; i++)
    {
      /* vty_out (vty, "argv[%d] - %s%s", i, argv[i], VTY_NEWLINE); */

      switch (argv[i][0])
	{

	case 'a':
	  if (i > 2 || strncmp (argv[i], "authentication-", 15) == 0)
	    {
	      /* authentication-key - this option can occur anywhere on 
		                      command line.  At start of command line
				      must check for authentication option. */
	      memset (auth_key, 0, OSPF_AUTH_SIMPLE_SIZE + 1);
	      vl_config.auth_key = auth_key;
	    }
	  else if (strncmp (argv[i], "authentication", 14) == 0)
	    {
	      /* authentication  - this option can only occur at start
		                   of command line */
	      vl_config.auth_type = OSPF_AUTH_NOTSET;
	    }
	  break;

	case 'm':
	  /* message-digest-key */
	  /* Delete one key */
	  i++;
	  vl_config.crypto_key_id = strtol (argv[i], NULL, 10);
	  if (vl_config.crypto_key_id < 0)
	    return CMD_WARNING;
	  vl_config.md5_key = NULL; 
	  break;

	case 'h':
	  /* Hello interval */
	  vl_config.hello_interval = OSPF_HELLO_INTERVAL_DEFAULT;
	  break;

	case 'r':
	  /* Retransmit Interval */
	  vl_config.retransmit_interval = OSPF_RETRANSMIT_INTERVAL_DEFAULT;
	  break;

	case 't':
	  /* Transmit Delay */
	  vl_config.transmit_delay = OSPF_TRANSMIT_DELAY_DEFAULT;
	  break;

	case 'd':
	  /* Dead Interval */
	  i++;
	  vl_config.dead_interval = OSPF_ROUTER_DEAD_INTERVAL_DEFAULT;
	  break;
	}
    }


  /* Action configuration */

  return ospf_vl_set (ospf, &vl_config);
}

ALIAS (ospf_area_vlink,
       ospf_area_vlink_param1_cmd,
       "area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) <1-65535>",
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_TIME_PARAM)

ALIAS (no_ospf_area_vlink,
       no_ospf_area_vlink_param1_cmd,
       "no area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval)",
       NO_STR
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_TIME_PARAM)

ALIAS (ospf_area_vlink,
       ospf_area_vlink_param2_cmd,
       "area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) <1-65535> "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) <1-65535>",
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_TIME_PARAM
       VLINK_HELPSTR_TIME_PARAM)

ALIAS (no_ospf_area_vlink,
       no_ospf_area_vlink_param2_cmd,
       "no area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval)",
       NO_STR
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_TIME_PARAM
       VLINK_HELPSTR_TIME_PARAM)

ALIAS (ospf_area_vlink,
       ospf_area_vlink_param3_cmd,
       "area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) <1-65535> "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) <1-65535> "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) <1-65535>",
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_TIME_PARAM
       VLINK_HELPSTR_TIME_PARAM
       VLINK_HELPSTR_TIME_PARAM)

ALIAS (no_ospf_area_vlink,
       no_ospf_area_vlink_param3_cmd,
       "no area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval)",
       NO_STR
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_TIME_PARAM
       VLINK_HELPSTR_TIME_PARAM
       VLINK_HELPSTR_TIME_PARAM)

ALIAS (ospf_area_vlink,
       ospf_area_vlink_param4_cmd,
       "area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) <1-65535> "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) <1-65535> "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) <1-65535> "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) <1-65535>",
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_TIME_PARAM
       VLINK_HELPSTR_TIME_PARAM
       VLINK_HELPSTR_TIME_PARAM
       VLINK_HELPSTR_TIME_PARAM)

ALIAS (no_ospf_area_vlink,
       no_ospf_area_vlink_param4_cmd,
       "no area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval) "
       "(hello-interval|retransmit-interval|transmit-delay|dead-interval)",
       NO_STR
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_TIME_PARAM
       VLINK_HELPSTR_TIME_PARAM
       VLINK_HELPSTR_TIME_PARAM
       VLINK_HELPSTR_TIME_PARAM)

ALIAS (ospf_area_vlink,
       ospf_area_vlink_authtype_args_cmd,
       "area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(authentication|) (message-digest|null)",
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_AUTHTYPE_ALL)

ALIAS (ospf_area_vlink,
       ospf_area_vlink_authtype_cmd,
       "area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(authentication|)",
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_AUTHTYPE_SIMPLE)

ALIAS (no_ospf_area_vlink,
       no_ospf_area_vlink_authtype_cmd,
       "no area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(authentication|)",
       NO_STR
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_AUTHTYPE_SIMPLE)

ALIAS (ospf_area_vlink,
       ospf_area_vlink_md5_cmd,
       "area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(message-digest-key|) <1-255> md5 KEY",
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_AUTH_MD5)

ALIAS (no_ospf_area_vlink,
       no_ospf_area_vlink_md5_cmd,
       "no area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(message-digest-key|) <1-255>",
       NO_STR
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_AUTH_MD5)

ALIAS (ospf_area_vlink,
       ospf_area_vlink_authkey_cmd,
       "area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(authentication-key|) AUTH_KEY",
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_AUTH_SIMPLE)

ALIAS (no_ospf_area_vlink,
       no_ospf_area_vlink_authkey_cmd,
       "no area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(authentication-key|)",
       NO_STR
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_AUTH_SIMPLE)

ALIAS (ospf_area_vlink,
       ospf_area_vlink_authtype_args_authkey_cmd,
       "area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(authentication|) (message-digest|null) "
       "(authentication-key|) AUTH_KEY",
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_AUTHTYPE_ALL
       VLINK_HELPSTR_AUTH_SIMPLE)

ALIAS (ospf_area_vlink,
       ospf_area_vlink_authtype_authkey_cmd,
       "area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(authentication|) "
       "(authentication-key|) AUTH_KEY",
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_AUTHTYPE_SIMPLE
       VLINK_HELPSTR_AUTH_SIMPLE)

ALIAS (no_ospf_area_vlink,
       no_ospf_area_vlink_authtype_authkey_cmd,
       "no area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(authentication|) "
       "(authentication-key|)",
       NO_STR
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_AUTHTYPE_SIMPLE
       VLINK_HELPSTR_AUTH_SIMPLE)

ALIAS (ospf_area_vlink,
       ospf_area_vlink_authtype_args_md5_cmd,
       "area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(authentication|) (message-digest|null) "
       "(message-digest-key|) <1-255> md5 KEY",
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_AUTHTYPE_ALL
       VLINK_HELPSTR_AUTH_MD5)

ALIAS (ospf_area_vlink,
       ospf_area_vlink_authtype_md5_cmd,
       "area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(authentication|) "
       "(message-digest-key|) <1-255> md5 KEY",
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_AUTHTYPE_SIMPLE
       VLINK_HELPSTR_AUTH_MD5)

ALIAS (no_ospf_area_vlink,
       no_ospf_area_vlink_authtype_md5_cmd,
       "no area (A.B.C.D|<0-4294967295>) virtual-link A.B.C.D "
       "(authentication|) "
       "(message-digest-key|)",
       NO_STR
       VLINK_HELPSTR_IPADDR
       VLINK_HELPSTR_AUTHTYPE_SIMPLE
       VLINK_HELPSTR_AUTH_MD5)


DEFUN (ospf_area_shortcut,
       ospf_area_shortcut_cmd,
       "area (A.B.C.D|<0-4294967295>) shortcut (default|enable|disable)",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Configure the area's shortcutting mode\n"
       "Set default shortcutting behavior\n"
       "Enable shortcutting through the area\n"
       "Disable shortcutting through the area\n")
{
  struct ospf *ospf = vty->index;
  struct ospf_area *area;
  struct in_addr area_id;
  int mode;
  int format;

  VTY_GET_OSPF_AREA_ID_NO_BB ("shortcut", area_id, format, argv[0]);

  area = ospf_area_get (ospf, area_id, format);

  if (strncmp (argv[1], "de", 2) == 0)
    mode = OSPF_SHORTCUT_DEFAULT;
  else if (strncmp (argv[1], "di", 2) == 0)
    mode = OSPF_SHORTCUT_DISABLE;
  else if (strncmp (argv[1], "e", 1) == 0)
    mode = OSPF_SHORTCUT_ENABLE;
  else
    return CMD_WARNING;

  ospf_area_shortcut_set (ospf, area, mode);

  if (ospf->abr_type != OSPF_ABR_SHORTCUT)
    vty_out (vty, "Shortcut area setting will take effect "
	     "only when the router is configured as Shortcut ABR%s",
	     VTY_NEWLINE);

  return CMD_SUCCESS;
}

DEFUN (no_ospf_area_shortcut,
       no_ospf_area_shortcut_cmd,
       "no area (A.B.C.D|<0-4294967295>) shortcut (enable|disable)",
       NO_STR
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Deconfigure the area's shortcutting mode\n"
       "Deconfigure enabled shortcutting through the area\n"
       "Deconfigure disabled shortcutting through the area\n")
{
  struct ospf *ospf = vty->index;
  struct ospf_area *area;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID_NO_BB ("shortcut", area_id, format, argv[0]);

  area = ospf_area_lookup_by_area_id (ospf, area_id);
  if (!area)
    return CMD_SUCCESS;

  ospf_area_shortcut_unset (ospf, area);

  return CMD_SUCCESS;
}


DEFUN (ospf_area_stub,
       ospf_area_stub_cmd,
       "area (A.B.C.D|<0-4294967295>) stub",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Configure OSPF area as stub\n")
{
  struct ospf *ospf = vty->index;
  struct in_addr area_id;
  int ret, format;

  VTY_GET_OSPF_AREA_ID_NO_BB ("stub", area_id, format, argv[0]);

  ret = ospf_area_stub_set (ospf, area_id);
  if (ret == 0)
    {
      vty_out (vty, "First deconfigure all virtual link through this area%s",
	       VTY_NEWLINE);
      return CMD_WARNING;
    }

  ospf_area_no_summary_unset (ospf, area_id);

  return CMD_SUCCESS;
}

DEFUN (ospf_area_stub_no_summary,
       ospf_area_stub_no_summary_cmd,
       "area (A.B.C.D|<0-4294967295>) stub no-summary",
       "OSPF stub parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Configure OSPF area as stub\n"
       "Do not inject inter-area routes into stub\n")
{
  struct ospf *ospf = vty->index;
  struct in_addr area_id;
  int ret, format;

  VTY_GET_OSPF_AREA_ID_NO_BB ("stub", area_id, format, argv[0]);

  ret = ospf_area_stub_set (ospf, area_id);
  if (ret == 0)
    {
      vty_out (vty, "%% Area cannot be stub as it contains a virtual link%s",
	       VTY_NEWLINE);
      return CMD_WARNING;
    }

  ospf_area_no_summary_set (ospf, area_id);

  return CMD_SUCCESS;
}

DEFUN (no_ospf_area_stub,
       no_ospf_area_stub_cmd,
       "no area (A.B.C.D|<0-4294967295>) stub",
       NO_STR
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Configure OSPF area as stub\n")
{
  struct ospf *ospf = vty->index;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID_NO_BB ("stub", area_id, format, argv[0]);

  ospf_area_stub_unset (ospf, area_id);
  ospf_area_no_summary_unset (ospf, area_id);

  return CMD_SUCCESS;
}

DEFUN (no_ospf_area_stub_no_summary,
       no_ospf_area_stub_no_summary_cmd,
       "no area (A.B.C.D|<0-4294967295>) stub no-summary",
       NO_STR
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Configure OSPF area as stub\n"
       "Do not inject inter-area routes into area\n")
{
  struct ospf *ospf = vty->index;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID_NO_BB ("stub", area_id, format, argv[0]);
  ospf_area_no_summary_unset (ospf, area_id);

  return CMD_SUCCESS;
}

static int
ospf_area_nssa_cmd_handler (struct vty *vty, int argc, const char *argv[], 
                            int nosum)
{
  struct ospf *ospf = vty->index;
  struct in_addr area_id;
  int ret, format;

  VTY_GET_OSPF_AREA_ID_NO_BB ("NSSA", area_id, format, argv[0]);

  ret = ospf_area_nssa_set (ospf, area_id);
  if (ret == 0)
    {
      vty_out (vty, "%% Area cannot be nssa as it contains a virtual link%s",
	       VTY_NEWLINE);
      return CMD_WARNING;
    }

  if (argc > 1)
    {
      if (strncmp (argv[1], "translate-c", 11) == 0)
        ospf_area_nssa_translator_role_set (ospf, area_id,
					    OSPF_NSSA_ROLE_CANDIDATE);
      else if (strncmp (argv[1], "translate-n", 11) == 0)
        ospf_area_nssa_translator_role_set (ospf, area_id,
					    OSPF_NSSA_ROLE_NEVER);
      else if (strncmp (argv[1], "translate-a", 11) == 0)
        ospf_area_nssa_translator_role_set (ospf, area_id,
					    OSPF_NSSA_ROLE_ALWAYS);
    }
  else
    {
      ospf_area_nssa_translator_role_set (ospf, area_id,
                        OSPF_NSSA_ROLE_CANDIDATE);
    }

  if (nosum)
    ospf_area_no_summary_set (ospf, area_id);
  else
    ospf_area_no_summary_unset (ospf, area_id);

  ospf_schedule_abr_task (ospf);
    
  return CMD_SUCCESS;
}

DEFUN (ospf_area_nssa_translate_no_summary,
       ospf_area_nssa_translate_no_summary_cmd,
       "area (A.B.C.D|<0-4294967295>) nssa (translate-candidate|translate-never|translate-always) no-summary",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Configure OSPF area as nssa\n"
       "Configure NSSA-ABR for translate election (default)\n"
       "Configure NSSA-ABR to never translate\n"
       "Configure NSSA-ABR to always translate\n"
       "Do not inject inter-area routes into nssa\n")
{
   return ospf_area_nssa_cmd_handler (vty, argc, argv, 1);
}

DEFUN (ospf_area_nssa_translate,
       ospf_area_nssa_translate_cmd,
       "area (A.B.C.D|<0-4294967295>) nssa (translate-candidate|translate-never|translate-always)",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Configure OSPF area as nssa\n"
       "Configure NSSA-ABR for translate election (default)\n"
       "Configure NSSA-ABR to never translate\n"
       "Configure NSSA-ABR to always translate\n")
{
  return ospf_area_nssa_cmd_handler (vty, argc, argv, 0);
}

DEFUN (ospf_area_nssa,
       ospf_area_nssa_cmd,
       "area (A.B.C.D|<0-4294967295>) nssa",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Configure OSPF area as nssa\n")
{
  return ospf_area_nssa_cmd_handler (vty, argc, argv, 0);
}

DEFUN (ospf_area_nssa_no_summary,
       ospf_area_nssa_no_summary_cmd,
       "area (A.B.C.D|<0-4294967295>) nssa no-summary",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Configure OSPF area as nssa\n"
       "Do not inject inter-area routes into nssa\n")
{
  return ospf_area_nssa_cmd_handler (vty, argc, argv, 1);
}

DEFUN (no_ospf_area_nssa,
       no_ospf_area_nssa_cmd,
       "no area (A.B.C.D|<0-4294967295>) nssa",
       NO_STR
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Configure OSPF area as nssa\n")
{
  struct ospf *ospf = vty->index;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID_NO_BB ("NSSA", area_id, format, argv[0]);

  ospf_area_nssa_unset (ospf, area_id);
  ospf_area_no_summary_unset (ospf, area_id);

  ospf_schedule_abr_task (ospf);

  return CMD_SUCCESS;
}

DEFUN (no_ospf_area_nssa_no_summary,
       no_ospf_area_nssa_no_summary_cmd,
       "no area (A.B.C.D|<0-4294967295>) nssa no-summary",
       NO_STR
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Configure OSPF area as nssa\n"
       "Do not inject inter-area routes into nssa\n")
{
  struct ospf *ospf = vty->index;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID_NO_BB ("NSSA", area_id, format, argv[0]);
  ospf_area_no_summary_unset (ospf, area_id);

  return CMD_SUCCESS;
}

DEFUN (ospf_area_default_cost,
       ospf_area_default_cost_cmd,
       "area (A.B.C.D|<0-4294967295>) default-cost <0-16777215>",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Set the summary-default cost of a NSSA or stub area\n"
       "Stub's advertised default summary cost\n")
{
  struct ospf *ospf = vty->index;
  struct ospf_area *area;
  struct in_addr area_id;
  u_int32_t cost;
  int format;
  struct prefix_ipv4 p;

  VTY_GET_OSPF_AREA_ID_NO_BB ("default-cost", area_id, format, argv[0]);
  VTY_GET_INTEGER_RANGE ("stub default cost", cost, argv[1], 0, 16777215);

  area = ospf_area_get (ospf, area_id, format);

  if (area->external_routing == OSPF_AREA_DEFAULT)
    {
      vty_out (vty, "The area is neither stub, nor NSSA%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  area->default_cost = cost;

  p.family = AF_INET;
  p.prefix.s_addr = OSPF_DEFAULT_DESTINATION;
  p.prefixlen = 0;
  if (IS_DEBUG_OSPF_EVENT)
    zlog_debug ("ospf_abr_announce_stub_defaults(): "
                "announcing 0.0.0.0/0 to area %s",
               inet_ntoa (area->area_id));
  ospf_abr_announce_network_to_area (&p, area->default_cost, area);

  return CMD_SUCCESS;
}

DEFUN (no_ospf_area_default_cost,
       no_ospf_area_default_cost_cmd,
       "no area (A.B.C.D|<0-4294967295>) default-cost <0-16777215>",
       NO_STR
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Set the summary-default cost of a NSSA or stub area\n"
       "Stub's advertised default summary cost\n")
{
  struct ospf *ospf = vty->index;
  struct ospf_area *area;
  struct in_addr area_id;
  u_int32_t cost;
  int format;
  struct prefix_ipv4 p;

  VTY_GET_OSPF_AREA_ID_NO_BB ("default-cost", area_id, format, argv[0]);
  VTY_GET_INTEGER_RANGE ("stub default cost", cost, argv[1], 0, 16777215);

  area = ospf_area_lookup_by_area_id (ospf, area_id);
  if (area == NULL)
    return CMD_SUCCESS;

  if (area->external_routing == OSPF_AREA_DEFAULT)
    {
      vty_out (vty, "The area is neither stub, nor NSSA%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  area->default_cost = 1;

  p.family = AF_INET;
  p.prefix.s_addr = OSPF_DEFAULT_DESTINATION;
  p.prefixlen = 0;
  if (IS_DEBUG_OSPF_EVENT)
    zlog_debug ("ospf_abr_announce_stub_defaults(): "
                "announcing 0.0.0.0/0 to area %s",
               inet_ntoa (area->area_id));
  ospf_abr_announce_network_to_area (&p, area->default_cost, area);


  ospf_area_check_free (ospf, area_id);

  return CMD_SUCCESS;
}

DEFUN (ospf_area_export_list,
       ospf_area_export_list_cmd,
       "area (A.B.C.D|<0-4294967295>) export-list NAME",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Set the filter for networks announced to other areas\n"
       "Name of the access-list\n")
{
  struct ospf *ospf = vty->index;
  struct ospf_area *area;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID (area_id, format, argv[0]);

  area = ospf_area_get (ospf, area_id, format);
  ospf_area_export_list_set (ospf, area, argv[1]);

  return CMD_SUCCESS;
}

DEFUN (no_ospf_area_export_list,
       no_ospf_area_export_list_cmd,
       "no area (A.B.C.D|<0-4294967295>) export-list NAME",
       NO_STR
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Unset the filter for networks announced to other areas\n"
       "Name of the access-list\n")
{
  struct ospf *ospf = vty->index;
  struct ospf_area *area;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID (area_id, format, argv[0]);

  area = ospf_area_lookup_by_area_id (ospf, area_id);
  if (area == NULL)
    return CMD_SUCCESS;

  ospf_area_export_list_unset (ospf, area);

  return CMD_SUCCESS;
}


DEFUN (ospf_area_import_list,
       ospf_area_import_list_cmd,
       "area (A.B.C.D|<0-4294967295>) import-list NAME",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Set the filter for networks from other areas announced to the specified one\n"
       "Name of the access-list\n")
{
  struct ospf *ospf = vty->index;
  struct ospf_area *area;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID (area_id, format, argv[0]);

  area = ospf_area_get (ospf, area_id, format);
  ospf_area_import_list_set (ospf, area, argv[1]);

  return CMD_SUCCESS;
}

DEFUN (no_ospf_area_import_list,
       no_ospf_area_import_list_cmd,
       "no area (A.B.C.D|<0-4294967295>) import-list NAME",
       NO_STR
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Unset the filter for networks announced to other areas\n"
       "Name of the access-list\n")
{
  struct ospf *ospf = vty->index;
  struct ospf_area *area;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID (area_id, format, argv[0]);

  area = ospf_area_lookup_by_area_id (ospf, area_id);
  if (area == NULL)
    return CMD_SUCCESS;

  ospf_area_import_list_unset (ospf, area);

  return CMD_SUCCESS;
}

DEFUN (ospf_area_filter_list,
       ospf_area_filter_list_cmd,
       "area (A.B.C.D|<0-4294967295>) filter-list prefix WORD (in|out)",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Filter networks between OSPF areas\n"
       "Filter prefixes between OSPF areas\n"
       "Name of an IP prefix-list\n"
       "Filter networks sent to this area\n"
       "Filter networks sent from this area\n")
{
  struct ospf *ospf = vty->index;
  struct ospf_area *area;
  struct in_addr area_id;
  struct prefix_list *plist;
  int format;

  VTY_GET_OSPF_AREA_ID (area_id, format, argv[0]);

  area = ospf_area_get (ospf, area_id, format);
  plist = prefix_list_lookup (AFI_IP, argv[1]);
  if (strncmp (argv[2], "in", 2) == 0)
    {
      PREFIX_LIST_IN (area) = plist;
      if (PREFIX_NAME_IN (area))
	free (PREFIX_NAME_IN (area));

      PREFIX_NAME_IN (area) = strdup (argv[1]);
      ospf_schedule_abr_task (ospf);
    }
  else
    {
      PREFIX_LIST_OUT (area) = plist;
      if (PREFIX_NAME_OUT (area))
	free (PREFIX_NAME_OUT (area));

      PREFIX_NAME_OUT (area) = strdup (argv[1]);
      ospf_schedule_abr_task (ospf);
    }

  return CMD_SUCCESS;
}

DEFUN (no_ospf_area_filter_list,
       no_ospf_area_filter_list_cmd,
       "no area (A.B.C.D|<0-4294967295>) filter-list prefix WORD (in|out)",
       NO_STR
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Filter networks between OSPF areas\n"
       "Filter prefixes between OSPF areas\n"
       "Name of an IP prefix-list\n"
       "Filter networks sent to this area\n"
       "Filter networks sent from this area\n")
{
  struct ospf *ospf = vty->index;
  struct ospf_area *area;
  struct in_addr area_id;
  struct prefix_list *plist;
  int format;

  VTY_GET_OSPF_AREA_ID (area_id, format, argv[0]);

  if ((area = ospf_area_lookup_by_area_id (ospf, area_id)) == NULL)
    return CMD_SUCCESS;
  
  plist = prefix_list_lookup (AFI_IP, argv[1]);
  if (strncmp (argv[2], "in", 2) == 0)
    {
      if (PREFIX_NAME_IN (area))
	if (strcmp (PREFIX_NAME_IN (area), argv[1]) != 0)
	  return CMD_SUCCESS;

      PREFIX_LIST_IN (area) = NULL;
      if (PREFIX_NAME_IN (area))
	free (PREFIX_NAME_IN (area));

      PREFIX_NAME_IN (area) = NULL;

      ospf_schedule_abr_task (ospf);
    }
  else
    {
      if (PREFIX_NAME_OUT (area))
	if (strcmp (PREFIX_NAME_OUT (area), argv[1]) != 0)
	  return CMD_SUCCESS;

      PREFIX_LIST_OUT (area) = NULL;
      if (PREFIX_NAME_OUT (area))
	free (PREFIX_NAME_OUT (area));

      PREFIX_NAME_OUT (area) = NULL;

      ospf_schedule_abr_task (ospf);
    }

  return CMD_SUCCESS;
}


DEFUN (ospf_area_authentication_message_digest,
       ospf_area_authentication_message_digest_cmd,
       "area (A.B.C.D|<0-4294967295>) authentication message-digest",
       "OSPF area parameters\n"
       "Enable authentication\n"
       "Use message-digest authentication\n")
{
  struct ospf *ospf = vty->index;
  struct ospf_area *area;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID (area_id, format, argv[0]);

  area = ospf_area_get (ospf, area_id, format);
  area->auth_type = OSPF_AUTH_CRYPTOGRAPHIC;

  return CMD_SUCCESS;
}

DEFUN (ospf_area_authentication,
       ospf_area_authentication_cmd,
       "area (A.B.C.D|<0-4294967295>) authentication",
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Enable authentication\n")
{
  struct ospf *ospf = vty->index;
  struct ospf_area *area;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID (area_id, format, argv[0]);

  area = ospf_area_get (ospf, area_id, format);
  area->auth_type = OSPF_AUTH_SIMPLE;

  return CMD_SUCCESS;
}

DEFUN (no_ospf_area_authentication,
       no_ospf_area_authentication_cmd,
       "no area (A.B.C.D|<0-4294967295>) authentication",
       NO_STR
       "OSPF area parameters\n"
       "OSPF area ID in IP address format\n"
       "OSPF area ID as a decimal value\n"
       "Enable authentication\n")
{
  struct ospf *ospf = vty->index;
  struct ospf_area *area;
  struct in_addr area_id;
  int format;

  VTY_GET_OSPF_AREA_ID (area_id, format, argv[0]);

  area = ospf_area_lookup_by_area_id (ospf, area_id);
  if (area == NULL)
    return CMD_SUCCESS;

  area->auth_type = OSPF_AUTH_NULL;

  ospf_area_check_free (ospf, area_id);
  
  return CMD_SUCCESS;
}


DEFUN (ospf_abr_type,
       ospf_abr_type_cmd,
       "ospf abr-type (cisco|ibm|shortcut|standard)",
       "OSPF specific commands\n"
       "Set OSPF ABR type\n"
       "Alternative ABR, cisco implementation\n"
       "Alternative ABR, IBM implementation\n"
       "Shortcut ABR\n"
       "Standard behavior (RFC2328)\n")
{
  struct ospf *ospf = vty->index;
  u_char abr_type = OSPF_ABR_UNKNOWN;

  if (strncmp (argv[0], "c", 1) == 0)
    abr_type = OSPF_ABR_CISCO;
  else if (strncmp (argv[0], "i", 1) == 0)
    abr_type = OSPF_ABR_IBM;
  else if (strncmp (argv[0], "sh", 2) == 0)
    abr_type = OSPF_ABR_SHORTCUT;
  else if (strncmp (argv[0], "st", 2) == 0)
    abr_type = OSPF_ABR_STAND;
  else
    return CMD_WARNING;

  /* If ABR type value is changed, schedule ABR task. */
  if (ospf->abr_type != abr_type)
    {
      ospf->abr_type = abr_type;
      ospf_schedule_abr_task (ospf);
    }

  return CMD_SUCCESS;
}

DEFUN (no_ospf_abr_type,
       no_ospf_abr_type_cmd,
       "no ospf abr-type (cisco|ibm|shortcut|standard)",
       NO_STR
       "OSPF specific commands\n"
       "Set OSPF ABR type\n"
       "Alternative ABR, cisco implementation\n"
       "Alternative ABR, IBM implementation\n"
       "Shortcut ABR\n")
{
  struct ospf *ospf = vty->index;
  u_char abr_type = OSPF_ABR_UNKNOWN;

  if (strncmp (argv[0], "c", 1) == 0)
    abr_type = OSPF_ABR_CISCO;
  else if (strncmp (argv[0], "i", 1) == 0)
    abr_type = OSPF_ABR_IBM;
  else if (strncmp (argv[0], "sh", 2) == 0)
    abr_type = OSPF_ABR_SHORTCUT;
  else if (strncmp (argv[0], "st", 2) == 0)
    abr_type = OSPF_ABR_STAND;
  else
    return CMD_WARNING;

  /* If ABR type value is changed, schedule ABR task. */
  if (ospf->abr_type == abr_type)
    {
      ospf->abr_type = OSPF_ABR_DEFAULT;
      ospf_schedule_abr_task (ospf);
    }

  return CMD_SUCCESS;
}

DEFUN (ospf_log_adjacency_changes,
       ospf_log_adjacency_changes_cmd,
       "log-adjacency-changes",
       "Log changes in adjacency state\n")
{
  struct ospf *ospf = vty->index;

  SET_FLAG(ospf->config, OSPF_LOG_ADJACENCY_CHANGES);
  return CMD_SUCCESS;
}

DEFUN (ospf_log_adjacency_changes_detail,
       ospf_log_adjacency_changes_detail_cmd,
       "log-adjacency-changes detail",
       "Log changes in adjacency state\n"
       "Log all state changes\n")
{
  struct ospf *ospf = vty->index;

  SET_FLAG(ospf->config, OSPF_LOG_ADJACENCY_CHANGES);
  SET_FLAG(ospf->config, OSPF_LOG_ADJACENCY_DETAIL);
  return CMD_SUCCESS;
}

DEFUN (no_ospf_log_adjacency_changes,
       no_ospf_log_adjacency_changes_cmd,
       "no log-adjacency-changes",
       NO_STR
       "Log changes in adjacency state\n")
{
  struct ospf *ospf = vty->index;

  UNSET_FLAG(ospf->config, OSPF_LOG_ADJACENCY_DETAIL);
  UNSET_FLAG(ospf->config, OSPF_LOG_ADJACENCY_CHANGES);
  return CMD_SUCCESS;
}

DEFUN (no_ospf_log_adjacency_changes_detail,
       no_ospf_log_adjacency_changes_detail_cmd,
       "no log-adjacency-changes detail",
       NO_STR
       "Log changes in adjacency state\n"
       "Log all state changes\n")
{
  struct ospf *ospf = vty->index;

  UNSET_FLAG(ospf->config, OSPF_LOG_ADJACENCY_DETAIL);
  return CMD_SUCCESS;
}

DEFUN (ospf_compatible_rfc1583,
       ospf_compatible_rfc1583_cmd,
       "compatible rfc1583",
       "OSPF compatibility list\n"
       "compatible with RFC 1583\n")
{
  struct ospf *ospf = vty->index;

  if (!CHECK_FLAG (ospf->config, OSPF_RFC1583_COMPATIBLE))
    {
      SET_FLAG (ospf->config, OSPF_RFC1583_COMPATIBLE);
      ospf_spf_calculate_schedule (ospf);
    }
  return CMD_SUCCESS;
}

DEFUN (no_ospf_compatible_rfc1583,
       no_ospf_compatible_rfc1583_cmd,
       "no compatible rfc1583",
       NO_STR
       "OSPF compatibility list\n"
       "compatible with RFC 1583\n")
{
  struct ospf *ospf = vty->index;

  if (CHECK_FLAG (ospf->config, OSPF_RFC1583_COMPATIBLE))
    {
      UNSET_FLAG (ospf->config, OSPF_RFC1583_COMPATIBLE);
      ospf_spf_calculate_schedule (ospf);
    }
  return CMD_SUCCESS;
}

ALIAS (ospf_compatible_rfc1583,
       ospf_rfc1583_flag_cmd,
       "ospf rfc1583compatibility",
       "OSPF specific commands\n"
       "Enable the RFC1583Compatibility flag\n")

ALIAS (no_ospf_compatible_rfc1583,
       no_ospf_rfc1583_flag_cmd,
       "no ospf rfc1583compatibility",
       NO_STR
       "OSPF specific commands\n"
       "Disable the RFC1583Compatibility flag\n")

static int
ospf_timers_spf_set (struct vty *vty, unsigned int delay,
                     unsigned int hold,
                     unsigned int max)
{
  struct ospf *ospf = vty->index;
  
  ospf->spf_delay = delay;
  ospf->spf_holdtime = hold;
  ospf->spf_max_holdtime = max;
  
  return CMD_SUCCESS;
}

DEFUN (ospf_timers_throttle_spf,
       ospf_timers_throttle_spf_cmd,
       "timers throttle spf <0-600000> <0-600000> <0-600000>",
       "Adjust routing timers\n"
       "Throttling adaptive timer\n"
       "OSPF SPF timers\n"
       "Delay (msec) from first change received till SPF calculation\n"
       "Initial hold time (msec) between consecutive SPF calculations\n"
       "Maximum hold time (msec)\n")
{
  unsigned int delay, hold, max;
  
  if (argc != 3)
    {
      vty_out (vty, "Insufficient arguments%s", VTY_NEWLINE);
      return CMD_WARNING;
    }
  
  VTY_GET_INTEGER_RANGE ("SPF delay timer", delay, argv[0], 0, 600000);
  VTY_GET_INTEGER_RANGE ("SPF hold timer", hold, argv[1], 0, 600000);
  VTY_GET_INTEGER_RANGE ("SPF max-hold timer", max, argv[2], 0, 600000);
  
  return ospf_timers_spf_set (vty, delay, hold, max);
}

DEFUN_DEPRECATED (ospf_timers_spf,
       ospf_timers_spf_cmd,
       "timers spf <0-4294967295> <0-4294967295>",
       "Adjust routing timers\n"
       "OSPF SPF timers\n"
       "Delay (s) between receiving a change to SPF calculation\n"
       "Hold time (s) between consecutive SPF calculations\n")
{
  unsigned int delay, hold;
  
  if (argc != 2)
    {
      vty_out (vty, "Insufficient number of arguments%s", VTY_NEWLINE);
      return CMD_WARNING;
    }
  
  VTY_GET_INTEGER ("SPF delay timer", delay, argv[0]);
  VTY_GET_INTEGER ("SPF hold timer", hold, argv[1]);
  
  /* truncate down the second values if they're greater than 600000ms */
  if (delay > (600000 / 1000))
    delay = 600000;
  else if (delay == 0)
    /* 0s delay was probably specified because of lack of ms resolution */
    delay = OSPF_SPF_DELAY_DEFAULT;
  if (hold > (600000 / 1000))
    hold = 600000;
      
  return ospf_timers_spf_set (vty, delay * 1000, hold * 1000, hold * 1000);
}

DEFUN (no_ospf_timers_throttle_spf,
       no_ospf_timers_throttle_spf_cmd,
       "no timers throttle spf",
       NO_STR
       "Adjust routing timers\n"
       "Throttling adaptive timer\n"
       "OSPF SPF timers\n")
{
  return ospf_timers_spf_set (vty,
                              OSPF_SPF_DELAY_DEFAULT,
                              OSPF_SPF_HOLDTIME_DEFAULT,
                              OSPF_SPF_MAX_HOLDTIME_DEFAULT);
}

ALIAS_DEPRECATED (no_ospf_timers_throttle_spf,
                  no_ospf_timers_spf_cmd,
                  "no timers spf",
                  NO_STR
                  "Adjust routing timers\n"
                  "OSPF SPF timers\n")

DEFUN (ospf_neighbor,
       ospf_neighbor_cmd,
       "neighbor A.B.C.D",
       NEIGHBOR_STR
       "Neighbor IP address\n")
{
  struct ospf *ospf = vty->index;
  struct in_addr nbr_addr;
  unsigned int priority = OSPF_NEIGHBOR_PRIORITY_DEFAULT;
  unsigned int interval = OSPF_POLL_INTERVAL_DEFAULT;

  VTY_GET_IPV4_ADDRESS ("neighbor address", nbr_addr, argv[0]);

  if (argc > 1)
    VTY_GET_INTEGER_RANGE ("neighbor priority", priority, argv[1], 0, 255);

  if (argc > 2)
    VTY_GET_INTEGER_RANGE ("poll interval", interval, argv[2], 1, 65535);

  ospf_nbr_nbma_set (ospf, nbr_addr);
  if (argc > 1)
    ospf_nbr_nbma_priority_set (ospf, nbr_addr, priority);
  if (argc > 2)
    ospf_nbr_nbma_poll_interval_set (ospf, nbr_addr, priority);

  return CMD_SUCCESS;
}

ALIAS (ospf_neighbor,
       ospf_neighbor_priority_poll_interval_cmd,
       "neighbor A.B.C.D priority <0-255> poll-interval <1-65535>",
       NEIGHBOR_STR
       "Neighbor IP address\n"
       "Neighbor Priority\n"
       "Priority\n"
       "Dead Neighbor Polling interval\n"
       "Seconds\n")

ALIAS (ospf_neighbor,
       ospf_neighbor_priority_cmd,
       "neighbor A.B.C.D priority <0-255>",
       NEIGHBOR_STR
       "Neighbor IP address\n"
       "Neighbor Priority\n"
       "Seconds\n")

DEFUN (ospf_neighbor_poll_interval,
       ospf_neighbor_poll_interval_cmd,
       "neighbor A.B.C.D poll-interval <1-65535>",
       NEIGHBOR_STR
       "Neighbor IP address\n"
       "Dead Neighbor Polling interval\n"
       "Seconds\n")
{
  struct ospf *ospf = vty->index;
  struct in_addr nbr_addr;
  unsigned int priority = OSPF_NEIGHBOR_PRIORITY_DEFAULT;
  unsigned int interval = OSPF_POLL_INTERVAL_DEFAULT;

  VTY_GET_IPV4_ADDRESS ("neighbor address", nbr_addr, argv[0]);

  if (argc > 1)
    VTY_GET_INTEGER_RANGE ("poll interval", interval, argv[1], 1, 65535);

  if (argc > 2)
    VTY_GET_INTEGER_RANGE ("neighbor priority", priority, argv[2], 0, 255);

  ospf_nbr_nbma_set (ospf, nbr_addr);
  if (argc > 1)
    ospf_nbr_nbma_poll_interval_set (ospf, nbr_addr, interval);
  if (argc > 2)
    ospf_nbr_nbma_priority_set (ospf, nbr_addr, priority);

  return CMD_SUCCESS;
}

ALIAS (ospf_neighbor_poll_interval,
       ospf_neighbor_poll_interval_priority_cmd,
       "neighbor A.B.C.D poll-interval <1-65535> priority <0-255>",
       NEIGHBOR_STR
       "Neighbor address\n"
       "OSPF dead-router polling interval\n"
       "Seconds\n"
       "OSPF priority of non-broadcast neighbor\n"
       "Priority\n")

DEFUN (no_ospf_neighbor,
       no_ospf_neighbor_cmd,
       "no neighbor A.B.C.D",
       NO_STR
       NEIGHBOR_STR
       "Neighbor IP address\n")
{
  struct ospf *ospf = vty->index;
  struct in_addr nbr_addr;
  int ret;

  VTY_GET_IPV4_ADDRESS ("neighbor address", nbr_addr, argv[0]);

  ret = ospf_nbr_nbma_unset (ospf, nbr_addr);

  return CMD_SUCCESS;
}

ALIAS (no_ospf_neighbor,
       no_ospf_neighbor_priority_cmd,
       "no neighbor A.B.C.D priority <0-255>",
       NO_STR
       NEIGHBOR_STR
       "Neighbor IP address\n"
       "Neighbor Priority\n"
       "Priority\n")

ALIAS (no_ospf_neighbor,
       no_ospf_neighbor_poll_interval_cmd,
       "no neighbor A.B.C.D poll-interval <1-65535>",
       NO_STR
       NEIGHBOR_STR
       "Neighbor IP address\n"
       "Dead Neighbor Polling interval\n"
       "Seconds\n")

ALIAS (no_ospf_neighbor,
       no_ospf_neighbor_priority_pollinterval_cmd,
       "no neighbor A.B.C.D priority <0-255> poll-interval <1-65535>",
       NO_STR
       NEIGHBOR_STR
       "Neighbor IP address\n"
       "Neighbor Priority\n"
       "Priority\n"
       "Dead Neighbor Polling interval\n"
       "Seconds\n")


DEFUN (ospf_refresh_timer, ospf_refresh_timer_cmd,
       "refresh timer <10-1800>",
       "Adjust refresh parameters\n"
       "Set refresh timer\n"
       "Timer value in seconds\n")
{
  struct ospf *ospf = vty->index;
  unsigned int interval;
  
  VTY_GET_INTEGER_RANGE ("refresh timer", interval, argv[0], 10, 1800);
  interval = (interval / 10) * 10;

  ospf_timers_refresh_set (ospf, interval);

  return CMD_SUCCESS;
}

DEFUN (no_ospf_refresh_timer, no_ospf_refresh_timer_val_cmd,
       "no refresh timer <10-1800>",
       "Adjust refresh parameters\n"
       "Unset refresh timer\n"
       "Timer value in seconds\n")
{
  struct ospf *ospf = vty->index;
  unsigned int interval;

  if (argc == 1)
    {
      VTY_GET_INTEGER_RANGE ("refresh timer", interval, argv[0], 10, 1800);
  
      if (ospf->lsa_refresh_interval != interval ||
	  interval == OSPF_LSA_REFRESH_INTERVAL_DEFAULT)
	return CMD_SUCCESS;
    }

  ospf_timers_refresh_unset (ospf);

  return CMD_SUCCESS;
}

ALIAS (no_ospf_refresh_timer,
       no_ospf_refresh_timer_cmd,
       "no refresh timer",
       "Adjust refresh parameters\n"
       "Unset refresh timer\n")

DEFUN (ospf_auto_cost_reference_bandwidth,
       ospf_auto_cost_reference_bandwidth_cmd,
       "auto-cost reference-bandwidth <1-4294967>",
       "Calculate OSPF interface cost according to bandwidth\n"
       "Use reference bandwidth method to assign OSPF cost\n"
       "The reference bandwidth in terms of Mbits per second\n")
{
  struct ospf *ospf = vty->index;
  u_int32_t refbw;
  struct listnode *node;
  struct interface *ifp;

  refbw = strtol (argv[0], NULL, 10);
  if (refbw < 1 || refbw > 4294967)
    {
      vty_out (vty, "reference-bandwidth value is invalid%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  /* If reference bandwidth is changed. */
  if ((refbw * 1000) == ospf->ref_bandwidth)
    return CMD_SUCCESS;
  
  ospf->ref_bandwidth = refbw * 1000;
  for (ALL_LIST_ELEMENTS_RO (om->iflist, node, ifp))
    ospf_if_recalculate_output_cost (ifp);
  
  return CMD_SUCCESS;
}

DEFUN (no_ospf_auto_cost_reference_bandwidth,
       no_ospf_auto_cost_reference_bandwidth_cmd,
       "no auto-cost reference-bandwidth",
       NO_STR
       "Calculate OSPF interface cost according to bandwidth\n"
       "Use reference bandwidth method to assign OSPF cost\n")
{
  struct ospf *ospf = vty->index;
  struct listnode *node, *nnode;
  struct interface *ifp;

  if (ospf->ref_bandwidth == OSPF_DEFAULT_REF_BANDWIDTH)
    return CMD_SUCCESS;
  
  ospf->ref_bandwidth = OSPF_DEFAULT_REF_BANDWIDTH;
  vty_out (vty, "%% OSPF: Reference bandwidth is changed.%s", VTY_NEWLINE);
  vty_out (vty, "        Please ensure reference bandwidth is consistent across all routers%s", VTY_NEWLINE);

  for (ALL_LIST_ELEMENTS (om->iflist, node, nnode, ifp))
    ospf_if_recalculate_output_cost (ifp);
      
  return CMD_SUCCESS;
}

const char *ospf_abr_type_descr_str[] = 
{
  "Unknown",
  "Standard (RFC2328)",
  "Alternative IBM",
  "Alternative Cisco",
  "Alternative Shortcut"
};

const char *ospf_shortcut_mode_descr_str[] = 
{
  "Default",
  "Enabled",
  "Disabled"
};



static void
show_ip_ospf_area (struct vty *vty, struct ospf_area *area)
{
  /* Show Area ID. */
  vty_out (vty, " Area ID: %s", inet_ntoa (area->area_id));

  /* Show Area type/mode. */
  if (OSPF_IS_AREA_BACKBONE (area))
    vty_out (vty, " (Backbone)%s", VTY_NEWLINE);
  else
    {
      if (area->external_routing == OSPF_AREA_STUB)
        vty_out (vty, " (Stub%s%s)",
		         area->no_summary ? ", no summary" : "",
		         area->shortcut_configured ? "; " : "");

      else if (area->external_routing == OSPF_AREA_NSSA)
        vty_out (vty, " (NSSA%s%s)",
                 area->no_summary ? ", no summary" : "",
                 area->shortcut_configured ? "; " : "");

      vty_out (vty, "%s", VTY_NEWLINE);
      vty_out (vty, "   Shortcutting mode: %s",
               ospf_shortcut_mode_descr_str[area->shortcut_configured]);
      vty_out (vty, ", S-bit consensus: %s%s",
               area->shortcut_capability ? "ok" : "no", VTY_NEWLINE);
    }

  /* Show number of interfaces. */
  vty_out (vty, "   Number of interfaces in this area: Total: %d, "
	   "Active: %d%s", listcount (area->oiflist),
	   area->act_ints, VTY_NEWLINE);

  if (area->external_routing == OSPF_AREA_NSSA)
    {
      vty_out (vty, "   It is an NSSA configuration. %s   Elected NSSA/ABR performs type-7/type-5 LSA translation. %s", VTY_NEWLINE, VTY_NEWLINE);
      if (! IS_OSPF_ABR (area->ospf))
        vty_out (vty, "   It is not ABR, therefore not Translator. %s",
                 VTY_NEWLINE);
      else if (area->NSSATranslatorState)
       {
         vty_out (vty, "   We are an ABR and ");
         if (area->NSSATranslatorRole == OSPF_NSSA_ROLE_CANDIDATE)
           vty_out (vty, "the NSSA Elected Translator. %s", 
	                VTY_NEWLINE);
         else if (area->NSSATranslatorRole == OSPF_NSSA_ROLE_ALWAYS)
           vty_out (vty, "always an NSSA Translator. %s",
                    VTY_NEWLINE);
       }
      else
       {
         vty_out (vty, "   We are an ABR, but ");
         if (area->NSSATranslatorRole == OSPF_NSSA_ROLE_CANDIDATE)
           vty_out (vty, "not the NSSA Elected Translator. %s",
                    VTY_NEWLINE);
         else
           vty_out (vty, "never an NSSA Translator. %s", 
	             VTY_NEWLINE);
	   }
    }
  /* Stub-router state for this area */
  if (CHECK_FLAG (area->stub_router_state, OSPF_AREA_IS_STUB_ROUTED))
    {
      char timebuf[OSPF_TIME_DUMP_SIZE];
      vty_out (vty, "   Originating stub / maximum-distance Router-LSA%s",
               VTY_NEWLINE);
      if (CHECK_FLAG(area->stub_router_state, OSPF_AREA_ADMIN_STUB_ROUTED))
        vty_out (vty, "     Administratively activated (indefinitely)%s",
                 VTY_NEWLINE);
      if (area->t_stub_router)
        vty_out (vty, "     Active from startup, %s remaining%s",
                 ospf_timer_dump (area->t_stub_router, timebuf, 
                                  sizeof(timebuf)), VTY_NEWLINE);
    }
  
  /* Show number of fully adjacent neighbors. */
  vty_out (vty, "   Number of fully adjacent neighbors in this area:"
                " %d%s", area->full_nbrs, VTY_NEWLINE);

  /* Show authentication type. */
  vty_out (vty, "   Area has ");
  if (area->auth_type == OSPF_AUTH_NULL)
    vty_out (vty, "no authentication%s", VTY_NEWLINE);
  else if (area->auth_type == OSPF_AUTH_SIMPLE)
    vty_out (vty, "simple password authentication%s", VTY_NEWLINE);
  else if (area->auth_type == OSPF_AUTH_CRYPTOGRAPHIC)
    vty_out (vty, "message digest authentication%s", VTY_NEWLINE);

  if (!OSPF_IS_AREA_BACKBONE (area))
    vty_out (vty, "   Number of full virtual adjacencies going through"
	     " this area: %d%s", area->full_vls, VTY_NEWLINE);

  /* Show SPF calculation times. */
  vty_out (vty, "   SPF algorithm executed %d times%s",
	   area->spf_calculation, VTY_NEWLINE);

  /* Show number of LSA. */
  vty_out (vty, "   Number of LSA %ld%s", area->lsdb->total, VTY_NEWLINE);
  vty_out (vty, "   Number of router LSA %ld. Checksum Sum 0x%08x%s",
	   ospf_lsdb_count (area->lsdb, OSPF_ROUTER_LSA),
	   ospf_lsdb_checksum (area->lsdb, OSPF_ROUTER_LSA), VTY_NEWLINE);
  vty_out (vty, "   Number of network LSA %ld. Checksum Sum 0x%08x%s",
           ospf_lsdb_count (area->lsdb, OSPF_NETWORK_LSA),
           ospf_lsdb_checksum (area->lsdb, OSPF_NETWORK_LSA), VTY_NEWLINE);
  vty_out (vty, "   Number of summary LSA %ld. Checksum Sum 0x%08x%s",
           ospf_lsdb_count (area->lsdb, OSPF_SUMMARY_LSA),
           ospf_lsdb_checksum (area->lsdb, OSPF_SUMMARY_LSA), VTY_NEWLINE);
  vty_out (vty, "   Number of ASBR summary LSA %ld. Checksum Sum 0x%08x%s",
           ospf_lsdb_count (area->lsdb, OSPF_ASBR_SUMMARY_LSA),
           ospf_lsdb_checksum (area->lsdb, OSPF_ASBR_SUMMARY_LSA), VTY_NEWLINE);
  vty_out (vty, "   Number of NSSA LSA %ld. Checksum Sum 0x%08x%s",
           ospf_lsdb_count (area->lsdb, OSPF_AS_NSSA_LSA),
           ospf_lsdb_checksum (area->lsdb, OSPF_AS_NSSA_LSA), VTY_NEWLINE);
#ifdef HAVE_OPAQUE_LSA
  vty_out (vty, "   Number of opaque link LSA %ld. Checksum Sum 0x%08x%s",
           ospf_lsdb_count (area->lsdb, OSPF_OPAQUE_LINK_LSA),
           ospf_lsdb_checksum (area->lsdb, OSPF_OPAQUE_LINK_LSA), VTY_NEWLINE);
  vty_out (vty, "   Number of opaque area LSA %ld. Checksum Sum 0x%08x%s",
           ospf_lsdb_count (area->lsdb, OSPF_OPAQUE_AREA_LSA),
           ospf_lsdb_checksum (area->lsdb, OSPF_OPAQUE_AREA_LSA), VTY_NEWLINE);
#endif /* HAVE_OPAQUE_LSA */
  vty_out (vty, "%s", VTY_NEWLINE);
}

DEFUN (show_ip_ospf,
       show_ip_ospf_cmd,
       "show ip ospf",
       SHOW_STR
       IP_STR
       "OSPF information\n")
{
  struct listnode *node, *nnode;
  struct ospf_area * area;
  struct ospf *ospf;
  struct timeval result;
  char timebuf[OSPF_TIME_DUMP_SIZE];

  /* Check OSPF is enable. */
  ospf = ospf_lookup ();
  if (ospf == NULL)
    {
      vty_out (vty, " OSPF Routing Process not enabled%s", VTY_NEWLINE);
      return CMD_SUCCESS;
    }

  /* Show Router ID. */
  vty_out (vty, " OSPF Routing Process, Router ID: %s%s",
           inet_ntoa (ospf->router_id),
           VTY_NEWLINE);
  
  /* Graceful shutdown */
  if (ospf->t_deferred_shutdown)
    vty_out (vty, " Deferred shutdown in progress, %s remaining%s",
             ospf_timer_dump (ospf->t_deferred_shutdown,
                              timebuf, sizeof (timebuf)), VTY_NEWLINE);
  /* Show capability. */
  vty_out (vty, " Supports only single TOS (TOS0) routes%s", VTY_NEWLINE);
  vty_out (vty, " This implementation conforms to RFC2328%s", VTY_NEWLINE);
  vty_out (vty, " RFC1583Compatibility flag is %s%s",
	   CHECK_FLAG (ospf->config, OSPF_RFC1583_COMPATIBLE) ?
	   "enabled" : "disabled", VTY_NEWLINE);
#ifdef HAVE_OPAQUE_LSA
  vty_out (vty, " OpaqueCapability flag is %s%s%s",
	   CHECK_FLAG (ospf->config, OSPF_OPAQUE_CAPABLE) ?
           "enabled" : "disabled",
           IS_OPAQUE_LSA_ORIGINATION_BLOCKED (ospf->opaque) ?
           " (origination blocked)" : "",
           VTY_NEWLINE);
#endif /* HAVE_OPAQUE_LSA */
  
  /* Show stub-router configuration */
  if (ospf->stub_router_startup_time != OSPF_STUB_ROUTER_UNCONFIGURED
      || ospf->stub_router_shutdown_time != OSPF_STUB_ROUTER_UNCONFIGURED)
    {
      vty_out (vty, " Stub router advertisement is configured%s",
               VTY_NEWLINE);
      if (ospf->stub_router_startup_time != OSPF_STUB_ROUTER_UNCONFIGURED)
        vty_out (vty, "   Enabled for %us after start-up%s",
                 ospf->stub_router_startup_time, VTY_NEWLINE);
      if (ospf->stub_router_shutdown_time != OSPF_STUB_ROUTER_UNCONFIGURED)
        vty_out (vty, "   Enabled for %us prior to full shutdown%s",
                 ospf->stub_router_shutdown_time, VTY_NEWLINE);
    }
  
  /* Show SPF timers. */
  vty_out (vty, " Initial SPF scheduling delay %d millisec(s)%s"
                " Minimum hold time between consecutive SPFs %d millisec(s)%s"
                " Maximum hold time between consecutive SPFs %d millisec(s)%s"
                " Hold time multiplier is currently %d%s",
	  ospf->spf_delay, VTY_NEWLINE,
	  ospf->spf_holdtime, VTY_NEWLINE,
	  ospf->spf_max_holdtime, VTY_NEWLINE,
	  ospf->spf_hold_multiplier, VTY_NEWLINE);
  vty_out (vty, " SPF algorithm ");
  if (ospf->ts_spf.tv_sec || ospf->ts_spf.tv_usec)
    {
      result = tv_sub (recent_relative_time (), ospf->ts_spf);
      vty_out (vty, "last executed %s ago%s",
               ospf_timeval_dump (&result, timebuf, sizeof (timebuf)),
               VTY_NEWLINE);
    }
  else
    vty_out (vty, "has not been run%s", VTY_NEWLINE);
  vty_out (vty, " SPF timer %s%s%s",
           (ospf->t_spf_calc ? "due in " : "is "),
           ospf_timer_dump (ospf->t_spf_calc, timebuf, sizeof (timebuf)),
           VTY_NEWLINE);
  
  /* Show refresh parameters. */
  vty_out (vty, " Refresh timer %d secs%s",
	   ospf->lsa_refresh_interval, VTY_NEWLINE);
	   
  /* Show ABR/ASBR flags. */
  if (CHECK_FLAG (ospf->flags, OSPF_FLAG_ABR))
    vty_out (vty, " This router is an ABR, ABR type is: %s%s",
             ospf_abr_type_descr_str[ospf->abr_type], VTY_NEWLINE);

  if (CHECK_FLAG (ospf->flags, OSPF_FLAG_ASBR))
    vty_out (vty, " This router is an ASBR "
             "(injecting external routing information)%s", VTY_NEWLINE);

  /* Show Number of AS-external-LSAs. */
  vty_out (vty, " Number of external LSA %ld. Checksum Sum 0x%08x%s",
	   ospf_lsdb_count (ospf->lsdb, OSPF_AS_EXTERNAL_LSA),
	   ospf_lsdb_checksum (ospf->lsdb, OSPF_AS_EXTERNAL_LSA), VTY_NEWLINE);
#ifdef HAVE_OPAQUE_LSA
  vty_out (vty, " Number of opaque AS LSA %ld. Checksum Sum 0x%08x%s",
	   ospf_lsdb_count (ospf->lsdb, OSPF_OPAQUE_AS_LSA),
	   ospf_lsdb_checksum (ospf->lsdb, OSPF_OPAQUE_AS_LSA), VTY_NEWLINE);
#endif /* HAVE_OPAQUE_LSA */
  /* Show number of areas attached. */
  vty_out (vty, " Number of areas attached to this router: %d%s",
           listcount (ospf->areas), VTY_NEWLINE);

  if (CHECK_FLAG(ospf->config, OSPF_LOG_ADJACENCY_CHANGES))
    {
      if (CHECK_FLAG(ospf->config, OSPF_LOG_ADJACENCY_DETAIL))
	vty_out(vty, " All adjacency changes are logged%s",VTY_NEWLINE);
      else
	vty_out(vty, " Adjacency changes are logged%s",VTY_NEWLINE);
    }

  vty_out (vty, "%s",VTY_NEWLINE);

  /* Show each area status. */
  for (ALL_LIST_ELEMENTS (ospf->areas, node, nnode, area))
    show_ip_ospf_area (vty, area);

  return CMD_SUCCESS;
}


static void
show_ip_ospf_interface_sub (struct vty *vty, struct ospf *ospf,
			    struct interface *ifp)
{
  int is_up;
  struct ospf_neighbor *nbr;
  struct route_node *rn;

  //zlog_debug("%s is %s", ifp->name,((is_up = if_is_operative(ifp)) ? "up" : "down"));

  /* Is interface up? */
  vty_out (vty, "%s is %s%s", ifp->name,
	   ((is_up = if_is_operative(ifp)) ? "up" : "down"), VTY_NEWLINE);
  vty_out (vty, "  ifindex %u, MTU %u bytes, BW %u Kbit %s%s",
  	   ifp->ifindex, ifp->mtu, ifp->bandwidth, if_flag_dump(ifp->flags),
	   VTY_NEWLINE);

  /* Is interface OSPF enabled? */
  if (ospf_oi_count(ifp) == 0)
    {
      vty_out (vty, "  OSPF not enabled on this interface%s", VTY_NEWLINE);
      return;
    }
  else if (!is_up)
    {
      vty_out (vty, "  OSPF is enabled, but not running on this interface%s",
	       VTY_NEWLINE);
      return;
    }

  for (rn = route_top (IF_OIFS (ifp)); rn; rn = route_next (rn))
    {
      struct ospf_interface *oi = rn->info;
      
      if (oi == NULL)
	      continue;
      //SE and OA interface don't have other params,will core dump in showing other
      if(oi->type == OSPF_IFTYPE_INTEROA || oi->type == OSPF_IFTYPE_SE)
      {
        vty_out (vty, "  Internet Address %s/%d,", inet_ntoa (oi->address->u.prefix4), oi->address->prefixlen);
        vty_out (vty, "  Transmit Delay is %d sec, State %s, Priority %d%s",OSPF_IF_PARAM (oi,transmit_delay), LOOKUP (ospf_ism_state_msg, oi->state), PRIORITY (oi), VTY_NEWLINE);
        continue;
      }
      //zlog_debug("  Internet Address %s/%d,", inet_ntoa (oi->address->u.prefix4), oi->address->prefixlen);

      /* Show OSPF interface information. */
      vty_out (vty, "  Internet Address %s/%d,",
	       inet_ntoa (oi->address->u.prefix4), oi->address->prefixlen);

      if (oi->connected->destination || oi->type == OSPF_IFTYPE_VIRTUALLINK)
        {
          struct in_addr *dest;
          const char *dstr;
          
	  if (CONNECTED_PEER(oi->connected)
	      || oi->type == OSPF_IFTYPE_VIRTUALLINK)
            dstr = "Peer";
          else
            dstr = "Broadcast";
          
          /* For Vlinks, showing the peer address is probably more
           * informative than the local interface that is being used
           */
          if (oi->type == OSPF_IFTYPE_VIRTUALLINK)
            dest = &oi->vl_data->peer_addr;
          else
            dest = &oi->connected->destination->u.prefix4;
          
	  vty_out (vty, " %s %s,", dstr, inet_ntoa (*dest));
        }

      vty_out (vty, " Area %s%s", ospf_area_desc_string (oi->area),
	       VTY_NEWLINE);

      vty_out (vty, "  MTU mismatch detection:%s%s",
           OSPF_IF_PARAM(oi, mtu_ignore) ? "disabled" : "enabled", VTY_NEWLINE);

      vty_out (vty, "  Router ID %s, Network Type %s, Cost: %d%s",
	       inet_ntoa (ospf->router_id), ospf_network_type_str[oi->type],
	       oi->output_cost, VTY_NEWLINE);

      vty_out (vty, "  Transmit Delay is %d sec, State %s, Priority %d%s",
	       OSPF_IF_PARAM (oi,transmit_delay), LOOKUP (ospf_ism_state_msg, oi->state),
	       PRIORITY (oi), VTY_NEWLINE);

  /* Show DR information. */
      if (DR (oi).s_addr == 0)
	vty_out (vty, "  No designated router on this network%s", VTY_NEWLINE);
      else
	{
	  nbr = ospf_nbr_lookup_by_addr (oi->nbrs, &DR (oi));
	  if (nbr == NULL)
	    vty_out (vty, "  No designated router on this network%s", VTY_NEWLINE);
	  else
	    {
	      vty_out (vty, "  Designated Router (ID) %s,",
		       inet_ntoa (nbr->router_id));
	      vty_out (vty, " Interface Address %s%s",
		       inet_ntoa (nbr->address.u.prefix4), VTY_NEWLINE);
	    }
	}

      /* Show BDR information. */
      if (BDR (oi).s_addr == 0)
	vty_out (vty, "  No backup designated router on this network%s",
		 VTY_NEWLINE);
      else
	{
	  nbr = ospf_nbr_lookup_by_addr (oi->nbrs, &BDR (oi));
	  if (nbr == NULL)
	    vty_out (vty, "  No backup designated router on this network%s",
		     VTY_NEWLINE);
	  else
	    {
	      vty_out (vty, "  Backup Designated Router (ID) %s,",
		       inet_ntoa (nbr->router_id));
	      vty_out (vty, " Interface Address %s%s",
		       inet_ntoa (nbr->address.u.prefix4), VTY_NEWLINE);
	    }
	}
      
      /* Next network-LSA sequence number we'll use, if we're elected DR */
      if (oi->params && ntohl (oi->params->network_lsa_seqnum)
                          != OSPF_INITIAL_SEQUENCE_NUMBER)
        vty_out (vty, "  Saved Network-LSA sequence number 0x%x%s",
                 ntohl (oi->params->network_lsa_seqnum), VTY_NEWLINE);
      
      vty_out (vty, "  Multicast group memberships:");
      if (OI_MEMBER_CHECK(oi, MEMBER_ALLROUTERS)
          || OI_MEMBER_CHECK(oi, MEMBER_DROUTERS))
        {
          if (OI_MEMBER_CHECK(oi, MEMBER_ALLROUTERS))
            vty_out (vty, " OSPFAllRouters");
          if (OI_MEMBER_CHECK(oi, MEMBER_DROUTERS))
            vty_out (vty, " OSPFDesignatedRouters");
        }
      else
        vty_out (vty, " <None>");
      vty_out (vty, "%s", VTY_NEWLINE);

      vty_out (vty, "  Timer intervals configured,");
      vty_out (vty, " Hello ");
      if (OSPF_IF_PARAM (oi, fast_hello) == 0)
        vty_out (vty, "%ds,", OSPF_IF_PARAM (oi, v_hello));
      else
        vty_out (vty, "%dms,", 1000 / OSPF_IF_PARAM (oi, fast_hello));
      vty_out (vty, " Dead %ds, Wait %ds, Retransmit %d%s",
	       OSPF_IF_PARAM (oi, v_wait),
	       OSPF_IF_PARAM (oi, v_wait),
	       OSPF_IF_PARAM (oi, retransmit_interval),
	       VTY_NEWLINE);
      
      if (OSPF_IF_PASSIVE_STATUS (oi) == OSPF_IF_ACTIVE)
        {
	  char timebuf[OSPF_TIME_DUMP_SIZE];
	  vty_out (vty, "    Hello due in %s%s",
		   ospf_timer_dump (oi->t_hello, timebuf, sizeof(timebuf)), 
		   VTY_NEWLINE);
        }
      else /* passive-interface is set */
	vty_out (vty, "    No Hellos (Passive interface)%s", VTY_NEWLINE);
      
      vty_out (vty, "  Neighbor Count is %d, Adjacent neighbor count is %d%s",
	       ospf_nbr_count (oi, 0), ospf_nbr_count (oi, NSM_Full),
	       VTY_NEWLINE);
    }
}

DEFUN (show_ip_ospf_interface,
       show_ip_ospf_interface_cmd,
       "show ip ospf interface [INTERFACE]",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "Interface information\n"
       "Interface name\n")
{
  struct interface *ifp;
  struct ospf *ospf;
  struct listnode *node;
  zlog_debug("in func show_ip_ospf_interface 1");
  ospf = ospf_lookup ();
  if (ospf == NULL)
    {
      vty_out (vty, "OSPF Routing Process not enabled%s", VTY_NEWLINE);
      return CMD_SUCCESS;
    }
  zlog_debug("in func show_ip_ospf_interface 2");
  /* Show All Interfaces. */
  if (argc == 0)
    for (ALL_LIST_ELEMENTS_RO (iflist, node, ifp))
      show_ip_ospf_interface_sub (vty, ospf, ifp);
  /* Interface name is specified. */
  else
    {
      if ((ifp = if_lookup_by_name (argv[0])) == NULL)
        vty_out (vty, "No such interface name%s", VTY_NEWLINE);
      else
        show_ip_ospf_interface_sub (vty, ospf, ifp);
    }

  return CMD_SUCCESS;
}

static void
show_ip_ospf_neighbour_header (struct vty *vty)
{
  vty_out (vty, "%s%15s %3s %-15s %9s %-15s %-20s %5s %5s %5s%s",
           VTY_NEWLINE,
           "Neighbor ID", "Pri", "State", "Dead Time",
           "Address", "Interface", "RXmtL", "RqstL", "DBsmL",
           VTY_NEWLINE);
}

static void
show_ip_ospf_neighbor_sub (struct vty *vty, struct ospf_interface *oi)
{
  struct route_node *rn;
  struct ospf_neighbor *nbr;
  char msgbuf[16];
  char timebuf[OSPF_TIME_DUMP_SIZE];

  for (rn = route_top (oi->nbrs); rn; rn = route_next (rn))
    if ((nbr = rn->info))
      /* Do not show myself. */
      if (nbr != oi->nbr_self)
	/* Down state is not shown. */
	if (nbr->state != NSM_Down)
	  {
	    ospf_nbr_state_message (nbr, msgbuf, 16);

	    if (nbr->state == NSM_Attempt && nbr->router_id.s_addr == 0)
	      vty_out (vty, "%-15s %3d %-15s ",
		       "-", nbr->priority,
		       msgbuf);
            else
	      vty_out (vty, "%-15s %3d %-15s ",
		       inet_ntoa (nbr->router_id), nbr->priority,
		       msgbuf);
            
            vty_out (vty, "%9s ",
                     ospf_timer_dump (nbr->t_inactivity, timebuf, 
                                      sizeof(timebuf)));
            
	    vty_out (vty, "%-15s ", inet_ntoa (nbr->src));
	    vty_out (vty, "%-20s %5ld %5ld %5d%s",
		     IF_NAME (oi), ospf_ls_retransmit_count (nbr),
		     ospf_ls_request_count (nbr), ospf_db_summary_count (nbr),
		     VTY_NEWLINE);
	  }
}

DEFUN (show_ip_ospf_neighbor,
       show_ip_ospf_neighbor_cmd,
       "show ip ospf neighbor",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "Neighbor list\n")
{
  struct ospf *ospf;
  struct ospf_interface *oi;
  struct listnode *node;

  ospf = ospf_lookup ();
  if (ospf == NULL)
    {
      vty_out (vty, " OSPF Routing Process not enabled%s", VTY_NEWLINE);
      return CMD_SUCCESS;
    }

  show_ip_ospf_neighbour_header (vty);

  for (ALL_LIST_ELEMENTS_RO (ospf->oiflist, node, oi))
    show_ip_ospf_neighbor_sub (vty, oi);

  return CMD_SUCCESS;
}

DEFUN (show_ip_ospf_neighbor_all,
       show_ip_ospf_neighbor_all_cmd,
       "show ip ospf neighbor all",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "Neighbor list\n"
       "include down status neighbor\n")
{
  struct ospf *ospf = ospf_lookup ();
  struct listnode *node;
  struct ospf_interface *oi;

  if (ospf == NULL)
    {
      vty_out (vty, " OSPF Routing Process not enabled%s", VTY_NEWLINE);
      return CMD_SUCCESS;
    }
  
  show_ip_ospf_neighbour_header (vty);
  
  for (ALL_LIST_ELEMENTS_RO (ospf->oiflist, node, oi))
    {
      struct listnode *nbr_node;
      struct ospf_nbr_nbma *nbr_nbma;

      show_ip_ospf_neighbor_sub (vty, oi);

    /* print Down neighbor status */
    for (ALL_LIST_ELEMENTS_RO (oi->nbr_nbma, nbr_node, nbr_nbma))
      {
	if (nbr_nbma->nbr == NULL
	    || nbr_nbma->nbr->state == NSM_Down)
	  {
	    vty_out (vty, "%-15s %3d %-15s %9s ",
		     "-", nbr_nbma->priority, "Down", "-");
	    vty_out (vty, "%-15s %-20s %5d %5d %5d%s", 
		     inet_ntoa (nbr_nbma->addr), IF_NAME (oi),
		     0, 0, 0, VTY_NEWLINE);
	  }
      }
    }

  return CMD_SUCCESS;
}

DEFUN (show_ip_ospf_neighbor_int,
       show_ip_ospf_neighbor_int_cmd,
       "show ip ospf neighbor IFNAME",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "Neighbor list\n"
       "Interface name\n")
{
  struct ospf *ospf;
  struct interface *ifp;
  struct route_node *rn;
 
  ifp = if_lookup_by_name (argv[0]);
  if (!ifp)
    {
      vty_out (vty, "No such interface.%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  ospf = ospf_lookup ();
  if (ospf == NULL)
    {
      vty_out (vty, " OSPF Routing Process not enabled%s", VTY_NEWLINE);
      return CMD_SUCCESS;
    }
  
  show_ip_ospf_neighbour_header (vty);
  
  for (rn = route_top (IF_OIFS (ifp)); rn; rn = route_next (rn))
    {
      struct ospf_interface *oi = rn->info;

      if (oi == NULL)
	continue;

      show_ip_ospf_neighbor_sub (vty, oi);
    }

  return CMD_SUCCESS;
}

static void
show_ip_ospf_nbr_nbma_detail_sub (struct vty *vty, struct ospf_interface *oi,
				  struct ospf_nbr_nbma *nbr_nbma)
{
  char timebuf[OSPF_TIME_DUMP_SIZE];

  /* Show neighbor ID. */
  vty_out (vty, " Neighbor %s,", "-");

  /* Show interface address. */
  vty_out (vty, " interface address %s%s",
	   inet_ntoa (nbr_nbma->addr), VTY_NEWLINE);
  /* Show Area ID. */
  vty_out (vty, "    In the area %s via interface %s%s",
	   ospf_area_desc_string (oi->area), IF_NAME (oi), VTY_NEWLINE);
  /* Show neighbor priority and state. */
  vty_out (vty, "    Neighbor priority is %d, State is %s,",
	   nbr_nbma->priority, "Down");
  /* Show state changes. */
  vty_out (vty, " %d state changes%s", nbr_nbma->state_change, VTY_NEWLINE);

  /* Show PollInterval */
  vty_out (vty, "    Poll interval %d%s", nbr_nbma->v_poll, VTY_NEWLINE);

  /* Show poll-interval timer. */
  vty_out (vty, "    Poll timer due in %s%s",
	   ospf_timer_dump (nbr_nbma->t_poll, timebuf, sizeof(timebuf)),
           VTY_NEWLINE);

  /* Show poll-interval timer thread. */
  vty_out (vty, "    Thread Poll Timer %s%s", 
	   nbr_nbma->t_poll != NULL ? "on" : "off", VTY_NEWLINE);
}

static void
show_ip_ospf_neighbor_detail_sub (struct vty *vty, struct ospf_interface *oi,
				  struct ospf_neighbor *nbr)
{
  char timebuf[OSPF_TIME_DUMP_SIZE];

  /* Show neighbor ID. */
  if (nbr->state == NSM_Attempt && nbr->router_id.s_addr == 0)
    vty_out (vty, " Neighbor %s,", "-");
  else
  vty_out (vty, " Neighbor %s,", inet_ntoa (nbr->router_id));

  /* Show interface address. */
  vty_out (vty, " interface address %s%s",
	   inet_ntoa (nbr->address.u.prefix4), VTY_NEWLINE);
  /* Show Area ID. */
  vty_out (vty, "    In the area %s via interface %s%s",
	   ospf_area_desc_string (oi->area), oi->ifp->name, VTY_NEWLINE);
  /* Show neighbor priority and state. */
  vty_out (vty, "    Neighbor priority is %d, State is %s,",
	   nbr->priority, LOOKUP (ospf_nsm_state_msg, nbr->state));
  /* Show state changes. */
  vty_out (vty, " %d state changes%s", nbr->state_change, VTY_NEWLINE);
  if (nbr->ts_last_progress.tv_sec || nbr->ts_last_progress.tv_usec)
    {
      struct timeval res
        = tv_sub (recent_relative_time (), nbr->ts_last_progress);
      vty_out (vty, "    Most recent state change statistics:%s",
               VTY_NEWLINE);
      vty_out (vty, "      Progressive change %s ago%s",
               ospf_timeval_dump (&res, timebuf, sizeof(timebuf)),
               VTY_NEWLINE);
    }
  if (nbr->ts_last_regress.tv_sec || nbr->ts_last_regress.tv_usec)
    {
      struct timeval res
        = tv_sub (recent_relative_time (), nbr->ts_last_regress);
      vty_out (vty, "      Regressive change %s ago, due to %s%s",
               ospf_timeval_dump (&res, timebuf, sizeof(timebuf)),
               (nbr->last_regress_str ? nbr->last_regress_str : "??"),
               VTY_NEWLINE);
    }
  /* Show Designated Rotuer ID. */
  vty_out (vty, "    DR is %s,", inet_ntoa (nbr->d_router));
  /* Show Backup Designated Rotuer ID. */
  vty_out (vty, " BDR is %s%s", inet_ntoa (nbr->bd_router), VTY_NEWLINE);
  /* Show options. */
  vty_out (vty, "    Options %d %s%s", nbr->options,
	   ospf_options_dump (nbr->options), VTY_NEWLINE);
  /* Show Router Dead interval timer. */
  vty_out (vty, "    Dead timer due in %s%s",
	   ospf_timer_dump (nbr->t_inactivity, timebuf, sizeof (timebuf)),
           VTY_NEWLINE);
  /* Show Database Summary list. */
  vty_out (vty, "    Database Summary List %d%s",
	   ospf_db_summary_count (nbr), VTY_NEWLINE);
  /* Show Link State Request list. */
  vty_out (vty, "    Link State Request List %ld%s",
	   ospf_ls_request_count (nbr), VTY_NEWLINE);
  /* Show Link State Retransmission list. */
  vty_out (vty, "    Link State Retransmission List %ld%s",
	   ospf_ls_retransmit_count (nbr), VTY_NEWLINE);
  /* Show inactivity timer thread. */
  vty_out (vty, "    Thread Inactivity Timer %s%s", 
	   nbr->t_inactivity != NULL ? "on" : "off", VTY_NEWLINE);
  /* Show Database Description retransmission thread. */
  vty_out (vty, "    Thread Database Description Retransmision %s%s",
	   nbr->t_db_desc != NULL ? "on" : "off", VTY_NEWLINE);
  /* Show Link State Request Retransmission thread. */
  vty_out (vty, "    Thread Link State Request Retransmission %s%s",
	   nbr->t_ls_req != NULL ? "on" : "off", VTY_NEWLINE);
  /* Show Link State Update Retransmission thread. */
  vty_out (vty, "    Thread Link State Update Retransmission %s%s%s",
	   nbr->t_ls_upd != NULL ? "on" : "off", VTY_NEWLINE, VTY_NEWLINE);
}

DEFUN (show_ip_ospf_neighbor_id,
       show_ip_ospf_neighbor_id_cmd,
       "show ip ospf neighbor A.B.C.D",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "Neighbor list\n"
       "Neighbor ID\n")
{
  struct ospf *ospf;
  struct listnode *node;
  struct ospf_neighbor *nbr;
  struct ospf_interface *oi;
  struct in_addr router_id;
  int ret;

  ret = inet_aton (argv[0], &router_id);
  if (!ret)
    {
      vty_out (vty, "Please specify Neighbor ID by A.B.C.D%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  ospf = ospf_lookup ();
  if (ospf == NULL)
    {
      vty_out (vty, " OSPF Routing Process not enabled%s", VTY_NEWLINE);
      return CMD_SUCCESS;
    }

  for (ALL_LIST_ELEMENTS_RO (ospf->oiflist, node, oi))
    if ((nbr = ospf_nbr_lookup_by_routerid (oi->nbrs, &router_id)))
      show_ip_ospf_neighbor_detail_sub (vty, oi, nbr);

  return CMD_SUCCESS;
}

DEFUN (show_ip_ospf_neighbor_detail,
       show_ip_ospf_neighbor_detail_cmd,
       "show ip ospf neighbor detail",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "Neighbor list\n"
       "detail of all neighbors\n")
{
  struct ospf *ospf;
  struct ospf_interface *oi;
  struct listnode *node;

  ospf = ospf_lookup ();
  if (ospf == NULL)
    {
      vty_out (vty, " OSPF Routing Process not enabled%s", VTY_NEWLINE);
      return CMD_SUCCESS;
    }

  for (ALL_LIST_ELEMENTS_RO (ospf->oiflist, node, oi))
    {
      struct route_node *rn;
      struct ospf_neighbor *nbr;

      for (rn = route_top (oi->nbrs); rn; rn = route_next (rn))
	if ((nbr = rn->info))
	  if (nbr != oi->nbr_self)
	    if (nbr->state != NSM_Down)
	      show_ip_ospf_neighbor_detail_sub (vty, oi, nbr);
    }

  return CMD_SUCCESS;
}

DEFUN (show_ip_ospf_neighbor_detail_all,
       show_ip_ospf_neighbor_detail_all_cmd,
       "show ip ospf neighbor detail all",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "Neighbor list\n"
       "detail of all neighbors\n"
       "include down status neighbor\n")
{
  struct ospf *ospf;
  struct listnode *node;
  struct ospf_interface *oi;

  ospf = ospf_lookup ();
  if (ospf == NULL)
    {
      vty_out (vty, " OSPF Routing Process not enabled%s", VTY_NEWLINE);
      return CMD_SUCCESS;
    }

  for (ALL_LIST_ELEMENTS_RO (ospf->oiflist, node, oi))
    {
      struct route_node *rn;
      struct ospf_neighbor *nbr;
      struct ospf_nbr_nbma *nbr_nbma;

      for (rn = route_top (oi->nbrs); rn; rn = route_next (rn))
	if ((nbr = rn->info))
	  if (nbr != oi->nbr_self)
	    if (oi->type == OSPF_IFTYPE_NBMA && nbr->state != NSM_Down)
	      show_ip_ospf_neighbor_detail_sub (vty, oi, rn->info);

      if (oi->type == OSPF_IFTYPE_NBMA)
	{
	  struct listnode *nd;

	  for (ALL_LIST_ELEMENTS_RO (oi->nbr_nbma, nd, nbr_nbma))
            if (nbr_nbma->nbr == NULL
                || nbr_nbma->nbr->state == NSM_Down)
              show_ip_ospf_nbr_nbma_detail_sub (vty, oi, nbr_nbma);
	}
    }

  return CMD_SUCCESS;
}

DEFUN (show_ip_ospf_neighbor_int_detail,
       show_ip_ospf_neighbor_int_detail_cmd,
       "show ip ospf neighbor IFNAME detail",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "Neighbor list\n"
       "Interface name\n"
       "detail of all neighbors")
{
  struct ospf *ospf;
  struct ospf_interface *oi;
  struct interface *ifp;
  struct route_node *rn, *nrn;
  struct ospf_neighbor *nbr;

  ifp = if_lookup_by_name (argv[0]);
  if (!ifp)
    {
      vty_out (vty, "No such interface.%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  ospf = ospf_lookup ();
  if (ospf == NULL)
    {
      vty_out (vty, " OSPF Routing Process not enabled%s", VTY_NEWLINE);
      return CMD_SUCCESS;
    }


  for (rn = route_top (IF_OIFS (ifp)); rn; rn = route_next (rn))
    if ((oi = rn->info))
      for (nrn = route_top (oi->nbrs); nrn; nrn = route_next (nrn))
	if ((nbr = nrn->info))
	  if (nbr != oi->nbr_self)
	    if (nbr->state != NSM_Down)
	      show_ip_ospf_neighbor_detail_sub (vty, oi, nbr);

  return CMD_SUCCESS;
}


/* Show functions */
static int
show_lsa_summary (struct vty *vty, struct ospf_lsa *lsa, int self)
{
  struct router_lsa *rl;
  struct summary_lsa *sl;
  struct as_external_lsa *asel;
  struct prefix_ipv4 p;

  if (lsa != NULL)
    /* If self option is set, check LSA self flag. */
    if (self == 0 || IS_LSA_SELF (lsa))
      {
	/* LSA common part show. */
	vty_out (vty, "%-15s ", inet_ntoa (lsa->data->id));
	vty_out (vty, "%-15s %4d 0x%08lx 0x%04x",
		 inet_ntoa (lsa->data->adv_router), LS_AGE (lsa),
		 (u_long)ntohl (lsa->data->ls_seqnum), ntohs (lsa->data->checksum));
	/* LSA specific part show. */
	switch (lsa->data->type)
	  {
	  case OSPF_ROUTER_LSA:
	    rl = (struct router_lsa *) lsa->data;
	    vty_out (vty, " %-d", ntohs (rl->links));
	    break;
	  case OSPF_SUMMARY_LSA:
	    sl = (struct summary_lsa *) lsa->data;

	    p.family = AF_INET;
	    p.prefix = sl->header.id;
	    p.prefixlen = ip_masklen (sl->mask);
	    apply_mask_ipv4 (&p);

	    vty_out (vty, " %s/%d", inet_ntoa (p.prefix), p.prefixlen);
	    break;
	  case OSPF_AS_EXTERNAL_LSA:
	  case OSPF_AS_NSSA_LSA:
	    asel = (struct as_external_lsa *) lsa->data;

	    p.family = AF_INET;
	    p.prefix = asel->header.id;
	    p.prefixlen = ip_masklen (asel->mask);
	    apply_mask_ipv4 (&p);

	    vty_out (vty, " %s %s/%d [0x%lx]",
		     IS_EXTERNAL_METRIC (asel->e[0].tos) ? "E2" : "E1",
		     inet_ntoa (p.prefix), p.prefixlen,
		     (u_long)ntohl (asel->e[0].route_tag));
	    break;
	  case OSPF_NETWORK_LSA:
	  case OSPF_ASBR_SUMMARY_LSA:
#ifdef HAVE_OPAQUE_LSA
	  case OSPF_OPAQUE_LINK_LSA:
	  case OSPF_OPAQUE_AREA_LSA:
	  case OSPF_OPAQUE_AS_LSA:
#endif /* HAVE_OPAQUE_LSA */
	  default:
	    break;
	  }
    
	vty_out (vty, VTY_NEWLINE);
  zlog_debug("in func show_lsa_summary,lsa->phase_count=%d",lsa->phase_count);
  if(lsa->phase_count!=0)
  {
    zlog_debug("in show_lsa_summary,lsa->phase_count:%d,lsa->type=%d",lsa->phase_count,lsa->data->type);

      //zlog_debug("in show_lsa_summary,lsa->links_count:%d",lsa->links_count);
    for(int i=0;i<lsa->links_count;++i)
    {
      for(int j=0;j<lsa->phase_count;++j)
      {
        vty_out(vty,"%d  ",lsa->phase_matrix[i][j]);
          //zlog_debug("in show_lsa_summary,lsa->phase_matrix[%d][%d]=%d",i,j,lsa->phase_matrix[i][j]);
      }
      vty_out(vty,"++  ");
    }
    vty_out(vty,"%s",VTY_NEWLINE);

  }
      }

  return 0;
}

static const char *show_database_desc[] =
{
  "unknown",
  "Router Link States",
  "Net Link States",
  "Summary Link States",
  "ASBR-Summary Link States",
  "AS External Link States",
  "Group Membership LSA",
  "NSSA-external Link States",
#ifdef HAVE_OPAQUE_LSA
  "Type-8 LSA",
  "Link-Local Opaque-LSA",
  "Area-Local Opaque-LSA",
  "AS-external Opaque-LSA",
#endif /* HAVE_OPAQUE_LSA */
};

static const char *show_database_header[] =
{
  "",
  "Link ID         ADV Router      Age  Seq#       CkSum  Link count",
  "Link ID         ADV Router      Age  Seq#       CkSum",
  "Link ID         ADV Router      Age  Seq#       CkSum  Route",
  "Link ID         ADV Router      Age  Seq#       CkSum",
  "Link ID         ADV Router      Age  Seq#       CkSum  Route",
  " --- header for Group Member ----",
  "Link ID         ADV Router      Age  Seq#       CkSum  Route",
#ifdef HAVE_OPAQUE_LSA
  " --- type-8 ---",
  "Opaque-Type/Id  ADV Router      Age  Seq#       CkSum",
  "Opaque-Type/Id  ADV Router      Age  Seq#       CkSum",
  "Opaque-Type/Id  ADV Router      Age  Seq#       CkSum",
#endif /* HAVE_OPAQUE_LSA */
};

static void
show_ip_ospf_database_header (struct vty *vty, struct ospf_lsa *lsa)
{
  struct router_lsa *rlsa = (struct router_lsa*) lsa->data;
  
  vty_out (vty, "  LS age: %d%s", LS_AGE (lsa), VTY_NEWLINE);
  vty_out (vty, "  Options: 0x%-2x : %s%s", 
           lsa->data->options,
           ospf_options_dump(lsa->data->options), 
           VTY_NEWLINE);
  vty_out (vty, "  LS Flags: 0x%-2x %s%s",
           lsa->flags,
           ((lsa->flags & OSPF_LSA_LOCAL_XLT) ? "(Translated from Type-7)" : ""),
           VTY_NEWLINE);

  if (lsa->data->type == OSPF_ROUTER_LSA)
    {
      vty_out (vty, "  Flags: 0x%x" , rlsa->flags);

      if (rlsa->flags)
	vty_out (vty, " :%s%s%s%s",
		 IS_ROUTER_LSA_BORDER (rlsa) ? " ABR" : "",
		 IS_ROUTER_LSA_EXTERNAL (rlsa) ? " ASBR" : "",
		 IS_ROUTER_LSA_VIRTUAL (rlsa) ? " VL-endpoint" : "",
		 IS_ROUTER_LSA_SHORTCUT (rlsa) ? " Shortcut" : "");

      vty_out (vty, "%s", VTY_NEWLINE);
    }
  vty_out (vty, "  LS Type: %s%s",
           LOOKUP (ospf_lsa_type_msg, lsa->data->type), VTY_NEWLINE);
  vty_out (vty, "  Link State ID: %s %s%s", inet_ntoa (lsa->data->id),
           LOOKUP (ospf_link_state_id_type_msg, lsa->data->type), VTY_NEWLINE);
  vty_out (vty, "  Advertising Router: %s%s",
           inet_ntoa (lsa->data->adv_router), VTY_NEWLINE);
  vty_out (vty, "  LS Seq Number: %08lx%s", (u_long)ntohl (lsa->data->ls_seqnum),
           VTY_NEWLINE);
  vty_out (vty, "  Checksum: 0x%04x%s", ntohs (lsa->data->checksum),
           VTY_NEWLINE);
  vty_out (vty, "  Length: %d%s", ntohs (lsa->data->length), VTY_NEWLINE);
}

const char *link_type_desc[] =
{
  "(null)",
  "another Router (point-to-point)",
  "a Transit Network",
  "Stub Network",
  "a Virtual Link",
  "a star earth link",
};

const char *link_id_desc[] =
{
  "(null)",
  "Neighboring Router ID",
  "Designated Router address",
  "Net",
  "Neighboring Router ID",
  "se link id",
};

const char *link_data_desc[] =
{
  "(null)",
  "Router Interface address",
  "Router Interface address",
  "Network Mask",
  "Router Interface address",
  "se link data",
};

/* Show router-LSA each Link information. */
static void
show_ip_ospf_database_router_links (struct vty *vty,
                                    struct router_lsa *rl)
{
  int len, i, type;

  len = ntohs (rl->header.length) - 4;
  for (i = 0; i < ntohs (rl->links) && len > 0; len -= 12, i++)
    {
      type = rl->link[i].type;

      vty_out (vty, "    Link connected to: %s%s",
	       link_type_desc[type], VTY_NEWLINE);
      vty_out (vty, "     (Link ID) %s: %s%s", link_id_desc[type],
	       inet_ntoa (rl->link[i].link_id), VTY_NEWLINE);
      vty_out (vty, "     (Link Data) %s: %s%s", link_data_desc[type],
	       inet_ntoa (rl->link[i].link_data), VTY_NEWLINE);
      vty_out (vty, "      Number of TOS metrics: 0%s", VTY_NEWLINE);
      vty_out (vty, "       TOS 0 Metric: %d%s",
	       ntohs (rl->link[i].metric), VTY_NEWLINE);
      vty_out (vty, "%s", VTY_NEWLINE);
    }
}

/* Show router-LSA detail information. */
static int
show_router_lsa_detail (struct vty *vty, struct ospf_lsa *lsa)
{
  if (lsa != NULL)
    {
      struct router_lsa *rl = (struct router_lsa *) lsa->data;

      show_ip_ospf_database_header (vty, lsa);
          
      vty_out (vty, "   Number of Links: %d%s%s", ntohs (rl->links),
	       VTY_NEWLINE, VTY_NEWLINE);

      show_ip_ospf_database_router_links (vty, rl);
      vty_out (vty, "%s", VTY_NEWLINE);
    }

  return 0;
}

/* Show network-LSA detail information. */
static int
show_network_lsa_detail (struct vty *vty, struct ospf_lsa *lsa)
{
  int length, i;

  if (lsa != NULL)
    {
      struct network_lsa *nl = (struct network_lsa *) lsa->data;

      show_ip_ospf_database_header (vty, lsa);

      vty_out (vty, "  Network Mask: /%d%s",
	       ip_masklen (nl->mask), VTY_NEWLINE);

      length = ntohs (lsa->data->length) - OSPF_LSA_HEADER_SIZE - 4;

      for (i = 0; length > 0; i++, length -= 4)
	vty_out (vty, "        Attached Router: %s%s",
		 inet_ntoa (nl->routers[i]), VTY_NEWLINE);

      vty_out (vty, "%s", VTY_NEWLINE);
    }

  return 0;
}

/* Show summary-LSA detail information. */
static int
show_summary_lsa_detail (struct vty *vty, struct ospf_lsa *lsa)
{
  if (lsa != NULL)
    {
      struct summary_lsa *sl = (struct summary_lsa *) lsa->data;

      show_ip_ospf_database_header (vty, lsa);

      vty_out (vty, "  Network Mask: /%d%s", ip_masklen (sl->mask),
	       VTY_NEWLINE);
      vty_out (vty, "        TOS: 0  Metric: %d%s", GET_METRIC (sl->metric),
	       VTY_NEWLINE);
	  vty_out (vty, "%s", VTY_NEWLINE);
    }

  return 0;
}

/* Show summary-ASBR-LSA detail information. */
static int
show_summary_asbr_lsa_detail (struct vty *vty, struct ospf_lsa *lsa)
{
  if (lsa != NULL)
    {
      struct summary_lsa *sl = (struct summary_lsa *) lsa->data;

      show_ip_ospf_database_header (vty, lsa);

      vty_out (vty, "  Network Mask: /%d%s",
	       ip_masklen (sl->mask), VTY_NEWLINE);
      vty_out (vty, "        TOS: 0  Metric: %d%s", GET_METRIC (sl->metric),
	       VTY_NEWLINE);
	  vty_out (vty, "%s", VTY_NEWLINE);
    }

  return 0;
}

/* Show AS-external-LSA detail information. */
static int
show_as_external_lsa_detail (struct vty *vty, struct ospf_lsa *lsa)
{
  if (lsa != NULL)
    {
      struct as_external_lsa *al = (struct as_external_lsa *) lsa->data;

      show_ip_ospf_database_header (vty, lsa);

      vty_out (vty, "  Network Mask: /%d%s",
	       ip_masklen (al->mask), VTY_NEWLINE);
      vty_out (vty, "        Metric Type: %s%s",
	       IS_EXTERNAL_METRIC (al->e[0].tos) ?
	       "2 (Larger than any link state path)" : "1", VTY_NEWLINE);
      vty_out (vty, "        TOS: 0%s", VTY_NEWLINE);
      vty_out (vty, "        Metric: %d%s",
	       GET_METRIC (al->e[0].metric), VTY_NEWLINE);
      vty_out (vty, "        Forward Address: %s%s",
	       inet_ntoa (al->e[0].fwd_addr), VTY_NEWLINE);

      vty_out (vty, "        External Route Tag: %lu%s%s",
	       (u_long)ntohl (al->e[0].route_tag), VTY_NEWLINE, VTY_NEWLINE);
    }

  return 0;
}

#if 0
static int
show_as_external_lsa_stdvty (struct ospf_lsa *lsa)
{
  struct as_external_lsa *al = (struct as_external_lsa *) lsa->data;

  /* show_ip_ospf_database_header (vty, lsa); */

  zlog_debug( "  Network Mask: /%d%s",
	     ip_masklen (al->mask), "\n");
  zlog_debug( "        Metric Type: %s%s",
	     IS_EXTERNAL_METRIC (al->e[0].tos) ?
	     "2 (Larger than any link state path)" : "1", "\n");
  zlog_debug( "        TOS: 0%s", "\n");
  zlog_debug( "        Metric: %d%s",
	     GET_METRIC (al->e[0].metric), "\n");
  zlog_debug( "        Forward Address: %s%s",
	     inet_ntoa (al->e[0].fwd_addr), "\n");

  zlog_debug( "        External Route Tag: %u%s%s",
	     ntohl (al->e[0].route_tag), "\n", "\n");

  return 0;
}
#endif

/* Show AS-NSSA-LSA detail information. */
static int
show_as_nssa_lsa_detail (struct vty *vty, struct ospf_lsa *lsa)
{
  if (lsa != NULL)
    {
      struct as_external_lsa *al = (struct as_external_lsa *) lsa->data;

      show_ip_ospf_database_header (vty, lsa);

      vty_out (vty, "  Network Mask: /%d%s",
	       ip_masklen (al->mask), VTY_NEWLINE);
      vty_out (vty, "        Metric Type: %s%s",
	       IS_EXTERNAL_METRIC (al->e[0].tos) ?
	       "2 (Larger than any link state path)" : "1", VTY_NEWLINE);
      vty_out (vty, "        TOS: 0%s", VTY_NEWLINE);
      vty_out (vty, "        Metric: %d%s",
	       GET_METRIC (al->e[0].metric), VTY_NEWLINE);
      vty_out (vty, "        NSSA: Forward Address: %s%s",
	       inet_ntoa (al->e[0].fwd_addr), VTY_NEWLINE);

      vty_out (vty, "        External Route Tag: %u%s%s",
	       ntohl (al->e[0].route_tag), VTY_NEWLINE, VTY_NEWLINE);
    }

  return 0;
}

static int
show_func_dummy (struct vty *vty, struct ospf_lsa *lsa)
{
  return 0;
}

#ifdef HAVE_OPAQUE_LSA
static int
show_opaque_lsa_detail (struct vty *vty, struct ospf_lsa *lsa)
{
  if (lsa != NULL)
    {
      show_ip_ospf_database_header (vty, lsa);
      show_opaque_info_detail (vty, lsa);

      vty_out (vty, "%s", VTY_NEWLINE);
    }
  return 0;
}
#endif /* HAVE_OPAQUE_LSA */

int (*show_function[])(struct vty *, struct ospf_lsa *) =
{
  NULL,
  show_router_lsa_detail,
  show_network_lsa_detail,
  show_summary_lsa_detail,
  show_summary_asbr_lsa_detail,
  show_as_external_lsa_detail,
  show_func_dummy,
  show_as_nssa_lsa_detail,  /* almost same as external */
#ifdef HAVE_OPAQUE_LSA
  NULL,				/* type-8 */
  show_opaque_lsa_detail,
  show_opaque_lsa_detail,
  show_opaque_lsa_detail,
#endif /* HAVE_OPAQUE_LSA */
};

static void
show_lsa_prefix_set (struct vty *vty, struct prefix_ls *lp, struct in_addr *id,
		     struct in_addr *adv_router)
{
  memset (lp, 0, sizeof (struct prefix_ls));
  lp->family = 0;
  if (id == NULL)
    lp->prefixlen = 0;
  else if (adv_router == NULL)
    {
      lp->prefixlen = 32;
      lp->id = *id;
    }
  else
    {
      lp->prefixlen = 64;
      lp->id = *id;
      lp->adv_router = *adv_router;
    }
}

static void
show_lsa_detail_proc (struct vty *vty, struct route_table *rt,
		      struct in_addr *id, struct in_addr *adv_router)
{
  struct prefix_ls lp;
  struct route_node *rn, *start;
  struct ospf_lsa *lsa;

  show_lsa_prefix_set (vty, &lp, id, adv_router);
  start = route_node_get (rt, (struct prefix *) &lp);
  if (start)
    {
      route_lock_node (start);
      for (rn = start; rn; rn = route_next_until (rn, start))
	if ((lsa = rn->info))
	  {
	    if (show_function[lsa->data->type] != NULL)
	      show_function[lsa->data->type] (vty, lsa);
	  }
      route_unlock_node (start);
    }
}

/* Show detail LSA information
   -- if id is NULL then show all LSAs. */
static void
show_lsa_detail (struct vty *vty, struct ospf *ospf, int type,
		 struct in_addr *id, struct in_addr *adv_router)
{
  struct listnode *node;
  struct ospf_area *area;
  
  switch (type)
    {
    case OSPF_AS_EXTERNAL_LSA:
#ifdef HAVE_OPAQUE_LSA
    case OSPF_OPAQUE_AS_LSA:
#endif /* HAVE_OPAQUE_LSA */
      vty_out (vty, "                %s %s%s",
               show_database_desc[type],
               VTY_NEWLINE, VTY_NEWLINE);
      show_lsa_detail_proc (vty, AS_LSDB (ospf, type), id, adv_router);
      break;
    default:
      for (ALL_LIST_ELEMENTS_RO (ospf->areas, node, area))
        {
          vty_out (vty, "%s                %s (Area %s)%s%s",
                   VTY_NEWLINE, show_database_desc[type],
                   ospf_area_desc_string (area), VTY_NEWLINE, VTY_NEWLINE);
          show_lsa_detail_proc (vty, AREA_LSDB (area, type), id, adv_router);
        }
      break;
    }
}

static void
show_lsa_detail_adv_router_proc (struct vty *vty, struct route_table *rt,
				 struct in_addr *adv_router)
{
  struct route_node *rn;
  struct ospf_lsa *lsa;

  for (rn = route_top (rt); rn; rn = route_next (rn))
    if ((lsa = rn->info))
      if (IPV4_ADDR_SAME (adv_router, &lsa->data->adv_router))
	{
	  if (CHECK_FLAG (lsa->flags, OSPF_LSA_LOCAL_XLT))
	    continue;
	  if (show_function[lsa->data->type] != NULL)
	    show_function[lsa->data->type] (vty, lsa);
	}
}

/* Show detail LSA information. */
static void
show_lsa_detail_adv_router (struct vty *vty, struct ospf *ospf, int type,
			    struct in_addr *adv_router)
{
  struct listnode *node;
  struct ospf_area *area;

  switch (type)
    {
    case OSPF_AS_EXTERNAL_LSA:
#ifdef HAVE_OPAQUE_LSA
    case OSPF_OPAQUE_AS_LSA:
#endif /* HAVE_OPAQUE_LSA */
      vty_out (vty, "                %s %s%s",
               show_database_desc[type],
               VTY_NEWLINE, VTY_NEWLINE);
      show_lsa_detail_adv_router_proc (vty, AS_LSDB (ospf, type),
                                       adv_router);
      break;
    default:
      for (ALL_LIST_ELEMENTS_RO (ospf->areas, node, area))
        {
          vty_out (vty, "%s                %s (Area %s)%s%s",
                   VTY_NEWLINE, show_database_desc[type],
                   ospf_area_desc_string (area), VTY_NEWLINE, VTY_NEWLINE);
          show_lsa_detail_adv_router_proc (vty, AREA_LSDB (area, type),
                                           adv_router);
	}
      break;
    }
}

static void
show_ip_ospf_database_summary (struct vty *vty, struct ospf *ospf, int self)
{
  struct ospf_lsa *lsa;
  struct route_node *rn;
  struct ospf_area *area;
  struct listnode *node;
  int type;

  for (ALL_LIST_ELEMENTS_RO (ospf->areas, node, area))
    {
      for (type = OSPF_MIN_LSA; type < OSPF_MAX_LSA; type++)
	{
	  switch (type)
	    {
	    case OSPF_AS_EXTERNAL_LSA:
#ifdef HAVE_OPAQUE_LSA
            case OSPF_OPAQUE_AS_LSA:
#endif /* HAVE_OPAQUE_LSA */
	      continue;
	    default:
	      break;
	    }
          if (ospf_lsdb_count_self (area->lsdb, type) > 0 ||
              (!self && ospf_lsdb_count (area->lsdb, type) > 0))
            {
              vty_out (vty, "                %s (Area %s)%s%s",
                       show_database_desc[type],
		       ospf_area_desc_string (area),
                       VTY_NEWLINE, VTY_NEWLINE);
              vty_out (vty, "%s%s", show_database_header[type], VTY_NEWLINE);

	      LSDB_LOOP (AREA_LSDB (area, type), rn, lsa)
		show_lsa_summary (vty, lsa, self);

              vty_out (vty, "%s", VTY_NEWLINE);
	  }
	}
    }

  for (type = OSPF_MIN_LSA; type < OSPF_MAX_LSA; type++)
    {
      switch (type)
        {
          case OSPF_AS_EXTERNAL_LSA:
#ifdef HAVE_OPAQUE_LSA
          case OSPF_OPAQUE_AS_LSA:
#endif /* HAVE_OPAQUE_LSA */
            break;
          default:
            continue;
        }
      if (ospf_lsdb_count_self (ospf->lsdb, type) ||
         (!self && ospf_lsdb_count (ospf->lsdb, type)))
        {
          vty_out (vty, "                %s%s%s",
	       show_database_desc[type],
	       VTY_NEWLINE, VTY_NEWLINE);
          vty_out (vty, "%s%s", show_database_header[type],
	       VTY_NEWLINE);

	  LSDB_LOOP (AS_LSDB (ospf, type), rn, lsa)
	    show_lsa_summary (vty, lsa, self);

          vty_out (vty, "%s", VTY_NEWLINE);
        }
    }

  vty_out (vty, "%s", VTY_NEWLINE);
}

static void
show_ip_ospf_database_maxage (struct vty *vty, struct ospf *ospf)
{
  struct listnode *node;
  struct ospf_lsa *lsa;

  vty_out (vty, "%s                MaxAge Link States:%s%s",
           VTY_NEWLINE, VTY_NEWLINE, VTY_NEWLINE);

  for (ALL_LIST_ELEMENTS_RO (ospf->maxage_lsa, node, lsa))
    {
      vty_out (vty, "Link type: %d%s", lsa->data->type, VTY_NEWLINE);
      vty_out (vty, "Link State ID: %s%s",
               inet_ntoa (lsa->data->id), VTY_NEWLINE);
      vty_out (vty, "Advertising Router: %s%s",
               inet_ntoa (lsa->data->adv_router), VTY_NEWLINE);
      vty_out (vty, "LSA lock count: %d%s", lsa->lock, VTY_NEWLINE);
      vty_out (vty, "%s", VTY_NEWLINE);
    }
}

#define OSPF_LSA_TYPE_NSSA_DESC      "NSSA external link state\n"
#define OSPF_LSA_TYPE_NSSA_CMD_STR   "|nssa-external"

#ifdef HAVE_OPAQUE_LSA
#define OSPF_LSA_TYPE_OPAQUE_LINK_DESC "Link local Opaque-LSA\n"
#define OSPF_LSA_TYPE_OPAQUE_AREA_DESC "Link area Opaque-LSA\n"
#define OSPF_LSA_TYPE_OPAQUE_AS_DESC   "Link AS Opaque-LSA\n"
#define OSPF_LSA_TYPE_OPAQUE_CMD_STR   "|opaque-link|opaque-area|opaque-as"
#else /* HAVE_OPAQUE_LSA */
#define OSPF_LSA_TYPE_OPAQUE_LINK_DESC ""
#define OSPF_LSA_TYPE_OPAQUE_AREA_DESC ""
#define OSPF_LSA_TYPE_OPAQUE_AS_DESC   ""
#define OSPF_LSA_TYPE_OPAQUE_CMD_STR   ""
#endif /* HAVE_OPAQUE_LSA */

#define OSPF_LSA_TYPES_CMD_STR                                                \
    "asbr-summary|external|network|router|summary"                            \
    OSPF_LSA_TYPE_NSSA_CMD_STR                                                \
    OSPF_LSA_TYPE_OPAQUE_CMD_STR

#define OSPF_LSA_TYPES_DESC                                                   \
   "ASBR summary link states\n"                                               \
   "External link states\n"                                                   \
   "Network link states\n"                                                    \
   "Router link states\n"                                                     \
   "Network summary link states\n"                                            \
   OSPF_LSA_TYPE_NSSA_DESC                                                    \
   OSPF_LSA_TYPE_OPAQUE_LINK_DESC                                             \
   OSPF_LSA_TYPE_OPAQUE_AREA_DESC                                             \
   OSPF_LSA_TYPE_OPAQUE_AS_DESC     

DEFUN (show_ip_ospf_database,
       show_ip_ospf_database_cmd,
       "show ip ospf database",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "Database summary\n")
{
  struct ospf *ospf;
  int type, ret;
  struct in_addr id, adv_router;

  ospf = ospf_lookup ();
  if (ospf == NULL)
    {
      vty_out (vty, " OSPF Routing Process not enabled%s", VTY_NEWLINE);
      return CMD_SUCCESS;
    }

  vty_out (vty, "%s       OSPF Router with ID (%s)%s%s", VTY_NEWLINE,
           inet_ntoa (ospf->router_id), VTY_NEWLINE, VTY_NEWLINE);

  /* Show all LSA. */
  if (argc == 0)
    {
      show_ip_ospf_database_summary (vty, ospf, 0);
      return CMD_SUCCESS;
    }

  /* Set database type to show. */
  if (strncmp (argv[0], "r", 1) == 0)
    type = OSPF_ROUTER_LSA;
  else if (strncmp (argv[0], "ne", 2) == 0)
    type = OSPF_NETWORK_LSA;
  else if (strncmp (argv[0], "ns", 2) == 0)
    type = OSPF_AS_NSSA_LSA;
  else if (strncmp (argv[0], "su", 2) == 0)
    type = OSPF_SUMMARY_LSA;
  else if (strncmp (argv[0], "a", 1) == 0)
    type = OSPF_ASBR_SUMMARY_LSA;
  else if (strncmp (argv[0], "e", 1) == 0)
    type = OSPF_AS_EXTERNAL_LSA;
  else if (strncmp (argv[0], "se", 2) == 0)
    {
      show_ip_ospf_database_summary (vty, ospf, 1);
      return CMD_SUCCESS;
    }
  else if (strncmp (argv[0], "m", 1) == 0)
    {
      show_ip_ospf_database_maxage (vty, ospf);
      return CMD_SUCCESS;
    }
#ifdef HAVE_OPAQUE_LSA
  else if (strncmp (argv[0], "opaque-l", 8) == 0)
    type = OSPF_OPAQUE_LINK_LSA;
  else if (strncmp (argv[0], "opaque-ar", 9) == 0)
    type = OSPF_OPAQUE_AREA_LSA;
  else if (strncmp (argv[0], "opaque-as", 9) == 0)
    type = OSPF_OPAQUE_AS_LSA;
#endif /* HAVE_OPAQUE_LSA */
  else
    return CMD_WARNING;

  /* `show ip ospf database LSA'. */
  if (argc == 1)
    show_lsa_detail (vty, ospf, type, NULL, NULL);
  else if (argc >= 2)
    {
      ret = inet_aton (argv[1], &id);
      if (!ret)
	return CMD_WARNING;
      
      /* `show ip ospf database LSA ID'. */
      if (argc == 2)
	show_lsa_detail (vty, ospf, type, &id, NULL);
      /* `show ip ospf database LSA ID adv-router ADV_ROUTER'. */
      else if (argc == 3)
	{
	  if (strncmp (argv[2], "s", 1) == 0)
	    adv_router = ospf->router_id;
	  else
	    {
	      ret = inet_aton (argv[2], &adv_router);
	      if (!ret)
		return CMD_WARNING;
	    }
	  show_lsa_detail (vty, ospf, type, &id, &adv_router);
	}
    }

  return CMD_SUCCESS;
}

ALIAS (show_ip_ospf_database,
       show_ip_ospf_database_type_cmd,
       "show ip ospf database (" OSPF_LSA_TYPES_CMD_STR "|max-age|self-originate)",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "Database summary\n"
       OSPF_LSA_TYPES_DESC
       "LSAs in MaxAge list\n"
       "Self-originated link states\n")

ALIAS (show_ip_ospf_database,
       show_ip_ospf_database_type_id_cmd,
       "show ip ospf database (" OSPF_LSA_TYPES_CMD_STR ") A.B.C.D",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "Database summary\n"
       OSPF_LSA_TYPES_DESC
       "Link State ID (as an IP address)\n")

ALIAS (show_ip_ospf_database,
       show_ip_ospf_database_type_id_adv_router_cmd,
       "show ip ospf database (" OSPF_LSA_TYPES_CMD_STR ") A.B.C.D adv-router A.B.C.D",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "Database summary\n"
       OSPF_LSA_TYPES_DESC
       "Link State ID (as an IP address)\n"
       "Advertising Router link states\n"
       "Advertising Router (as an IP address)\n")

ALIAS (show_ip_ospf_database,
       show_ip_ospf_database_type_id_self_cmd,
       "show ip ospf database (" OSPF_LSA_TYPES_CMD_STR ") A.B.C.D (self-originate|)",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "Database summary\n"
       OSPF_LSA_TYPES_DESC
       "Link State ID (as an IP address)\n"
       "Self-originated link states\n"
       "\n")

DEFUN (show_ip_ospf_database_type_adv_router,
       show_ip_ospf_database_type_adv_router_cmd,
       "show ip ospf database (" OSPF_LSA_TYPES_CMD_STR ") adv-router A.B.C.D",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "Database summary\n"
       OSPF_LSA_TYPES_DESC
       "Advertising Router link states\n"
       "Advertising Router (as an IP address)\n")
{
  struct ospf *ospf;
  int type, ret;
  struct in_addr adv_router;

  ospf = ospf_lookup ();
  if (ospf == NULL)
    {
      vty_out (vty, " OSPF Routing Process not enabled%s", VTY_NEWLINE);
      return CMD_SUCCESS;
    }

  vty_out (vty, "%s       OSPF Router with ID (%s)%s%s", VTY_NEWLINE,
           inet_ntoa (ospf->router_id), VTY_NEWLINE, VTY_NEWLINE);

  if (argc != 2)
    return CMD_WARNING;

  /* Set database type to show. */
  if (strncmp (argv[0], "r", 1) == 0)
    type = OSPF_ROUTER_LSA;
  else if (strncmp (argv[0], "ne", 2) == 0)
    type = OSPF_NETWORK_LSA;
  else if (strncmp (argv[0], "ns", 2) == 0)
    type = OSPF_AS_NSSA_LSA;
  else if (strncmp (argv[0], "s", 1) == 0)
    type = OSPF_SUMMARY_LSA;
  else if (strncmp (argv[0], "a", 1) == 0)
    type = OSPF_ASBR_SUMMARY_LSA;
  else if (strncmp (argv[0], "e", 1) == 0)
    type = OSPF_AS_EXTERNAL_LSA;
#ifdef HAVE_OPAQUE_LSA
  else if (strncmp (argv[0], "opaque-l", 8) == 0)
    type = OSPF_OPAQUE_LINK_LSA;
  else if (strncmp (argv[0], "opaque-ar", 9) == 0)
    type = OSPF_OPAQUE_AREA_LSA;
  else if (strncmp (argv[0], "opaque-as", 9) == 0)
    type = OSPF_OPAQUE_AS_LSA;
#endif /* HAVE_OPAQUE_LSA */
  else
    return CMD_WARNING;

  /* `show ip ospf database LSA adv-router ADV_ROUTER'. */
  if (strncmp (argv[1], "s", 1) == 0)
    adv_router = ospf->router_id;
  else
    {
      ret = inet_aton (argv[1], &adv_router);
      if (!ret)
	return CMD_WARNING;
    }

  show_lsa_detail_adv_router (vty, ospf, type, &adv_router);

  return CMD_SUCCESS;
}

ALIAS (show_ip_ospf_database_type_adv_router,
       show_ip_ospf_database_type_self_cmd,
       "show ip ospf database (" OSPF_LSA_TYPES_CMD_STR ") (self-originate|)",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "Database summary\n"
       OSPF_LSA_TYPES_DESC
       "Self-originated link states\n")


DEFUN (ip_ospf_authentication_args,
       ip_ospf_authentication_args_addr_cmd,
       "ip ospf authentication (null|message-digest) A.B.C.D",
       "IP Information\n"
       "OSPF interface commands\n"
       "Enable authentication on this interface\n"
       "Use null authentication\n"
       "Use message-digest authentication\n"
       "Address of interface")
{
  struct interface *ifp;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
  
  ifp = vty->index;
  params = IF_DEF_PARAMS (ifp);

  if (argc == 2)
    {
      ret = inet_aton(argv[1], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_get_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }

  /* Handle null authentication */
  if ( argv[0][0] == 'n' )
    {
      SET_IF_PARAM (params, auth_type);
      params->auth_type = OSPF_AUTH_NULL;
      return CMD_SUCCESS;
    }

  /* Handle message-digest authentication */
  if ( argv[0][0] == 'm' )
    {
      SET_IF_PARAM (params, auth_type);
      params->auth_type = OSPF_AUTH_CRYPTOGRAPHIC;
      return CMD_SUCCESS;
    }

  vty_out (vty, "You shouldn't get here!%s", VTY_NEWLINE);
  return CMD_WARNING;
}

ALIAS (ip_ospf_authentication_args,
       ip_ospf_authentication_args_cmd,
       "ip ospf authentication (null|message-digest)",
       "IP Information\n"
       "OSPF interface commands\n"
       "Enable authentication on this interface\n"
       "Use null authentication\n"
       "Use message-digest authentication\n")

DEFUN (ip_ospf_authentication,
       ip_ospf_authentication_addr_cmd,
       "ip ospf authentication A.B.C.D",
       "IP Information\n"
       "OSPF interface commands\n"
       "Enable authentication on this interface\n"
       "Address of interface")
{
  struct interface *ifp;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
  
  ifp = vty->index;
  params = IF_DEF_PARAMS (ifp);

  if (argc == 1)
    {
      ret = inet_aton(argv[0], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_get_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }
  
  SET_IF_PARAM (params, auth_type);
  params->auth_type = OSPF_AUTH_SIMPLE;

  return CMD_SUCCESS;
}

ALIAS (ip_ospf_authentication,
       ip_ospf_authentication_cmd,
       "ip ospf authentication",
       "IP Information\n"
       "OSPF interface commands\n"
       "Enable authentication on this interface\n")

DEFUN (no_ip_ospf_authentication,
       no_ip_ospf_authentication_addr_cmd,
       "no ip ospf authentication A.B.C.D",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Enable authentication on this interface\n"
       "Address of interface")
{
  struct interface *ifp;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
  
  ifp = vty->index;
  params = IF_DEF_PARAMS (ifp);

  if (argc == 1)
    {
      ret = inet_aton(argv[0], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_lookup_if_params (ifp, addr);
      if (params == NULL)
	return CMD_SUCCESS;
    }

  params->auth_type = OSPF_AUTH_NOTSET;
  UNSET_IF_PARAM (params, auth_type);
  
  if (params != IF_DEF_PARAMS (ifp))
    {
      ospf_free_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }
  
  return CMD_SUCCESS;
}

ALIAS (no_ip_ospf_authentication,
       no_ip_ospf_authentication_cmd,
       "no ip ospf authentication",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Enable authentication on this interface\n")

DEFUN (ip_ospf_authentication_key,
       ip_ospf_authentication_key_addr_cmd,
       "ip ospf authentication-key AUTH_KEY A.B.C.D",
       "IP Information\n"
       "OSPF interface commands\n"
       "Authentication password (key)\n"
       "The OSPF password (key)\n"
       "Address of interface")
{
  struct interface *ifp;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
  
  ifp = vty->index;
  params = IF_DEF_PARAMS (ifp);

  if (argc == 2)
    {
      ret = inet_aton(argv[1], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_get_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }


  memset (params->auth_simple, 0, OSPF_AUTH_SIMPLE_SIZE + 1);
  strncpy ((char *) params->auth_simple, argv[0], OSPF_AUTH_SIMPLE_SIZE);
  SET_IF_PARAM (params, auth_simple);

  return CMD_SUCCESS;
}

ALIAS (ip_ospf_authentication_key,
       ip_ospf_authentication_key_cmd,
       "ip ospf authentication-key AUTH_KEY",
       "IP Information\n"
       "OSPF interface commands\n"
       "Authentication password (key)\n"
       "The OSPF password (key)")

ALIAS (ip_ospf_authentication_key,
       ospf_authentication_key_cmd,
       "ospf authentication-key AUTH_KEY",
       "OSPF interface commands\n"
       "Authentication password (key)\n"
       "The OSPF password (key)")

DEFUN (no_ip_ospf_authentication_key,
       no_ip_ospf_authentication_key_addr_cmd,
       "no ip ospf authentication-key A.B.C.D",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Authentication password (key)\n"
       "Address of interface")
{
  struct interface *ifp;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
  
  ifp = vty->index;
  params = IF_DEF_PARAMS (ifp);

  if (argc == 1)
    {
      ret = inet_aton(argv[0], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_lookup_if_params (ifp, addr);
      if (params == NULL)
	return CMD_SUCCESS;
    }

  memset (params->auth_simple, 0, OSPF_AUTH_SIMPLE_SIZE);
  UNSET_IF_PARAM (params, auth_simple);
  
  if (params != IF_DEF_PARAMS (ifp))
    {
      ospf_free_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }
  
  return CMD_SUCCESS;
}

ALIAS (no_ip_ospf_authentication_key,
       no_ip_ospf_authentication_key_cmd,
       "no ip ospf authentication-key",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Authentication password (key)\n")

ALIAS (no_ip_ospf_authentication_key,
       no_ospf_authentication_key_cmd,
       "no ospf authentication-key",
       NO_STR
       "OSPF interface commands\n"
       "Authentication password (key)\n")

DEFUN (ip_ospf_message_digest_key,
       ip_ospf_message_digest_key_addr_cmd,
       "ip ospf message-digest-key <1-255> md5 KEY A.B.C.D",
       "IP Information\n"
       "OSPF interface commands\n"
       "Message digest authentication password (key)\n"
       "Key ID\n"
       "Use MD5 algorithm\n"
       "The OSPF password (key)"
       "Address of interface")
{
  struct interface *ifp;
  struct crypt_key *ck;
  u_char key_id;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
  
  ifp = vty->index;
  params = IF_DEF_PARAMS (ifp);

  if (argc == 3)
    {
      ret = inet_aton(argv[2], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_get_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }

  key_id = strtol (argv[0], NULL, 10);
  if (ospf_crypt_key_lookup (params->auth_crypt, key_id) != NULL)
    {
      vty_out (vty, "OSPF: Key %d already exists%s", key_id, VTY_NEWLINE);
      return CMD_WARNING;
    }

  ck = ospf_crypt_key_new ();
  ck->key_id = (u_char) key_id;
  memset (ck->auth_key, 0, OSPF_AUTH_MD5_SIZE+1);
  strncpy ((char *) ck->auth_key, argv[1], OSPF_AUTH_MD5_SIZE);

  ospf_crypt_key_add (params->auth_crypt, ck);
  SET_IF_PARAM (params, auth_crypt);
  
  return CMD_SUCCESS;
}

ALIAS (ip_ospf_message_digest_key,
       ip_ospf_message_digest_key_cmd,
       "ip ospf message-digest-key <1-255> md5 KEY",
       "IP Information\n"
       "OSPF interface commands\n"
       "Message digest authentication password (key)\n"
       "Key ID\n"
       "Use MD5 algorithm\n"
       "The OSPF password (key)")

ALIAS (ip_ospf_message_digest_key,
       ospf_message_digest_key_cmd,
       "ospf message-digest-key <1-255> md5 KEY",
       "OSPF interface commands\n"
       "Message digest authentication password (key)\n"
       "Key ID\n"
       "Use MD5 algorithm\n"
       "The OSPF password (key)")

DEFUN (no_ip_ospf_message_digest_key,
       no_ip_ospf_message_digest_key_addr_cmd,
       "no ip ospf message-digest-key <1-255> A.B.C.D",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Message digest authentication password (key)\n"
       "Key ID\n"
       "Address of interface")
{
  struct interface *ifp;
  struct crypt_key *ck;
  int key_id;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
  
  ifp = vty->index;
  params = IF_DEF_PARAMS (ifp);

  if (argc == 2)
    {
      ret = inet_aton(argv[1], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_lookup_if_params (ifp, addr);
      if (params == NULL)
	return CMD_SUCCESS;
    }

  key_id = strtol (argv[0], NULL, 10);
  ck = ospf_crypt_key_lookup (params->auth_crypt, key_id);
  if (ck == NULL)
    {
      vty_out (vty, "OSPF: Key %d does not exist%s", key_id, VTY_NEWLINE);
      return CMD_WARNING;
    }

  ospf_crypt_key_delete (params->auth_crypt, key_id);

  if (params != IF_DEF_PARAMS (ifp))
    {
      ospf_free_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }
  
  return CMD_SUCCESS;
}

ALIAS (no_ip_ospf_message_digest_key,
       no_ip_ospf_message_digest_key_cmd,
       "no ip ospf message-digest-key <1-255>",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Message digest authentication password (key)\n"
       "Key ID\n")
     
ALIAS (no_ip_ospf_message_digest_key,
       no_ospf_message_digest_key_cmd,
       "no ospf message-digest-key <1-255>",
       NO_STR
       "OSPF interface commands\n"
       "Message digest authentication password (key)\n"
       "Key ID\n")

DEFUN (ip_ospf_cost,
       ip_ospf_cost_u32_inet4_cmd,
       "ip ospf cost <1-65535> A.B.C.D",
       "IP Information\n"
       "OSPF interface commands\n"
       "Interface cost\n"
       "Cost\n"
       "Address of interface")
{
  struct interface *ifp = vty->index;
  u_int32_t cost;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
      
  params = IF_DEF_PARAMS (ifp);

  cost = strtol (argv[0], NULL, 10);

  /* cost range is <1-65535>. */
  if (cost < 1 || cost > 65535)
    {
      vty_out (vty, "Interface output cost is invalid%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  if (argc == 2)
    {
      ret = inet_aton(argv[1], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_get_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }

  SET_IF_PARAM (params, output_cost_cmd);
  params->output_cost_cmd = cost;

  ospf_if_recalculate_output_cost (ifp);
    
  return CMD_SUCCESS;
}

ALIAS (ip_ospf_cost,
       ip_ospf_cost_u32_cmd,
       "ip ospf cost <1-65535>",
       "IP Information\n"
       "OSPF interface commands\n"
       "Interface cost\n"
       "Cost")

ALIAS (ip_ospf_cost,
       ospf_cost_u32_cmd,
       "ospf cost <1-65535>",
       "OSPF interface commands\n"
       "Interface cost\n"
       "Cost")

ALIAS (ip_ospf_cost,
       ospf_cost_u32_inet4_cmd,
       "ospf cost <1-65535> A.B.C.D",
       "OSPF interface commands\n"
       "Interface cost\n"
       "Cost\n"
       "Address of interface")

DEFUN (no_ip_ospf_cost,
       no_ip_ospf_cost_inet4_cmd,
       "no ip ospf cost A.B.C.D",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Interface cost\n"
       "Address of interface")
{
  struct interface *ifp = vty->index;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
  
  ifp = vty->index;
  params = IF_DEF_PARAMS (ifp);

  if (argc == 1)
    {
      ret = inet_aton(argv[0], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_lookup_if_params (ifp, addr);
      if (params == NULL)
	return CMD_SUCCESS;
    }

  UNSET_IF_PARAM (params, output_cost_cmd);

  if (params != IF_DEF_PARAMS (ifp))
    {
      ospf_free_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }

  ospf_if_recalculate_output_cost (ifp);
  
  return CMD_SUCCESS;
}

ALIAS (no_ip_ospf_cost,
       no_ip_ospf_cost_cmd,
       "no ip ospf cost",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Interface cost\n")

ALIAS (no_ip_ospf_cost,
       no_ospf_cost_cmd,
       "no ospf cost",
       NO_STR
       "OSPF interface commands\n"
       "Interface cost\n")

ALIAS (no_ip_ospf_cost,
       no_ospf_cost_inet4_cmd,
       "no ospf cost A.B.C.D",
       NO_STR
       "OSPF interface commands\n"
       "Interface cost\n"
       "Address of interface")

DEFUN (no_ip_ospf_cost2,
       no_ip_ospf_cost_u32_cmd,
       "no ip ospf cost <1-65535>",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Interface cost\n"
       "Cost")
{
  struct interface *ifp = vty->index;
  struct in_addr addr;
  u_int32_t cost;
  int ret;
  struct ospf_if_params *params;

  ifp = vty->index;
  params = IF_DEF_PARAMS (ifp);

  /* According to the semantics we are mimicking "no ip ospf cost N" is
   * always treated as "no ip ospf cost" regardless of the actual value
   * of N already configured for the interface. Thus the first argument
   * is always checked to be a number, but is ignored after that.
   */
  cost = strtol (argv[0], NULL, 10);
  if (cost < 1 || cost > 65535)
    {
      vty_out (vty, "Interface output cost is invalid%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  if (argc == 2)
    {
      ret = inet_aton(argv[1], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_lookup_if_params (ifp, addr);
      if (params == NULL)
	return CMD_SUCCESS;
    }

  UNSET_IF_PARAM (params, output_cost_cmd);

  if (params != IF_DEF_PARAMS (ifp))
    {
      ospf_free_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }

  ospf_if_recalculate_output_cost (ifp);

  return CMD_SUCCESS;
}

ALIAS (no_ip_ospf_cost2,
       no_ospf_cost_u32_cmd,
       "no ospf cost <1-65535>",
       NO_STR
       "OSPF interface commands\n"
       "Interface cost\n"
       "Cost")

ALIAS (no_ip_ospf_cost2,
       no_ip_ospf_cost_u32_inet4_cmd,
       "no ip ospf cost <1-65535> A.B.C.D",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Interface cost\n"
       "Cost\n"
       "Address of interface")

ALIAS (no_ip_ospf_cost2,
       no_ospf_cost_u32_inet4_cmd,
       "no ospf cost <1-65535> A.B.C.D",
       NO_STR
       "OSPF interface commands\n"
       "Interface cost\n"
       "Cost\n"
       "Address of interface")

static void
ospf_nbr_timer_update (struct ospf_interface *oi)
{
  struct route_node *rn;
  struct ospf_neighbor *nbr;

  for (rn = route_top (oi->nbrs); rn; rn = route_next (rn))
    if ((nbr = rn->info))
      {
	nbr->v_inactivity = OSPF_IF_PARAM (oi, v_wait);
	nbr->v_db_desc = OSPF_IF_PARAM (oi, retransmit_interval);
	nbr->v_ls_req = OSPF_IF_PARAM (oi, retransmit_interval);
	nbr->v_ls_upd = OSPF_IF_PARAM (oi, retransmit_interval);
      }
}

static int
ospf_vty_dead_interval_set (struct vty *vty, const char *interval_str,
                            const char *nbr_str,
                            const char *fast_hello_str)
{
  struct interface *ifp = vty->index;
  u_int32_t seconds;
  u_char hellomult;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
  struct ospf_interface *oi;
  struct route_node *rn;
      
  params = IF_DEF_PARAMS (ifp);
  
  if (nbr_str)
    {
      ret = inet_aton(nbr_str, &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_get_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }

  if (interval_str)
    {
      VTY_GET_INTEGER_RANGE ("Router Dead Interval", seconds, interval_str,
                             1, 65535);
                             
      /* reset fast_hello too, just to be sure */
      UNSET_IF_PARAM (params, fast_hello);
      params->fast_hello = OSPF_FAST_HELLO_DEFAULT;
    }
  else if (fast_hello_str)
    {
      VTY_GET_INTEGER_RANGE ("Hello Multiplier", hellomult, fast_hello_str,
                             1, 10);
      /* 1s dead-interval with sub-second hellos desired */
      seconds = OSPF_ROUTER_DEAD_INTERVAL_MINIMAL;
      SET_IF_PARAM (params, fast_hello);
      params->fast_hello = hellomult;
    }
  else
    {
      vty_out (vty, "Please specify dead-interval or hello-multiplier%s",
              VTY_NEWLINE);
      return CMD_WARNING;
    }
    
  SET_IF_PARAM (params, v_wait);
  params->v_wait = seconds;
  
  /* Update timer values in neighbor structure. */
  if (nbr_str)
    {
      struct ospf *ospf;
      if ((ospf = ospf_lookup()))
	{
	  oi = ospf_if_lookup_by_local_addr (ospf, ifp, addr);
	  if (oi)
	    ospf_nbr_timer_update (oi);
	}
    }
  else
    {
      for (rn = route_top (IF_OIFS (ifp)); rn; rn = route_next (rn))
	if ((oi = rn->info))
	  ospf_nbr_timer_update (oi);
    }

  return CMD_SUCCESS;
}


DEFUN (ip_ospf_dead_interval,
       ip_ospf_dead_interval_addr_cmd,
       "ip ospf dead-interval <1-65535> A.B.C.D",
       "IP Information\n"
       "OSPF interface commands\n"
       "Interval after which a neighbor is declared dead\n"
       "Seconds\n"
       "Address of interface\n")
{
  if (argc == 2)
    return ospf_vty_dead_interval_set (vty, argv[0], argv[1], NULL);
  else
    return ospf_vty_dead_interval_set (vty, argv[0], NULL, NULL);
}

ALIAS (ip_ospf_dead_interval,
       ip_ospf_dead_interval_cmd,
       "ip ospf dead-interval <1-65535>",
       "IP Information\n"
       "OSPF interface commands\n"
       "Interval after which a neighbor is declared dead\n"
       "Seconds\n")

ALIAS (ip_ospf_dead_interval,
       ospf_dead_interval_cmd,
       "ospf dead-interval <1-65535>",
       "OSPF interface commands\n"
       "Interval after which a neighbor is declared dead\n"
       "Seconds\n")

DEFUN (ip_ospf_dead_interval_minimal,
       ip_ospf_dead_interval_minimal_addr_cmd,
       "ip ospf dead-interval minimal hello-multiplier <1-10> A.B.C.D",
       "IP Information\n"
       "OSPF interface commands\n"
       "Interval after which a neighbor is declared dead\n"
       "Minimal 1s dead-interval with fast sub-second hellos\n"
       "Hello multiplier factor\n"
       "Number of Hellos to send each second\n"
       "Address of interface\n")
{
  if (argc == 2)
    return ospf_vty_dead_interval_set (vty, NULL, argv[1], argv[0]);
  else
    return ospf_vty_dead_interval_set (vty, NULL, NULL, argv[0]);
}

ALIAS (ip_ospf_dead_interval_minimal,
       ip_ospf_dead_interval_minimal_cmd,
       "ip ospf dead-interval minimal hello-multiplier <1-10>",
       "IP Information\n"
       "OSPF interface commands\n"
       "Interval after which a neighbor is declared dead\n"
       "Minimal 1s dead-interval with fast sub-second hellos\n"
       "Hello multiplier factor\n"
       "Number of Hellos to send each second\n")

DEFUN (no_ip_ospf_dead_interval,
       no_ip_ospf_dead_interval_addr_cmd,
       "no ip ospf dead-interval A.B.C.D",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Interval after which a neighbor is declared dead\n"
       "Address of interface")
{
  struct interface *ifp = vty->index;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
  struct ospf_interface *oi;
  struct route_node *rn;

  ifp = vty->index;
  params = IF_DEF_PARAMS (ifp);

  if (argc == 1)
    {
      ret = inet_aton(argv[0], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_lookup_if_params (ifp, addr);
      if (params == NULL)
	return CMD_SUCCESS;
    }

  UNSET_IF_PARAM (params, v_wait);
  params->v_wait = OSPF_ROUTER_DEAD_INTERVAL_DEFAULT;
  
  UNSET_IF_PARAM (params, fast_hello);
  params->fast_hello = OSPF_FAST_HELLO_DEFAULT;
  
  if (params != IF_DEF_PARAMS (ifp))
    {
      ospf_free_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }

  /* Update timer values in neighbor structure. */
  if (argc == 1)
    {
      struct ospf *ospf;
      
      if ((ospf = ospf_lookup()))
	{
	  oi = ospf_if_lookup_by_local_addr (ospf, ifp, addr);
	  if (oi)
	    ospf_nbr_timer_update (oi);
	}
    }
  else
    {
      for (rn = route_top (IF_OIFS (ifp)); rn; rn = route_next (rn))
	if ((oi = rn->info))
	  ospf_nbr_timer_update (oi);
    }

  return CMD_SUCCESS;
}

ALIAS (no_ip_ospf_dead_interval,
       no_ip_ospf_dead_interval_cmd,
       "no ip ospf dead-interval",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Interval after which a neighbor is declared dead\n")

ALIAS (no_ip_ospf_dead_interval,
       no_ospf_dead_interval_cmd,
       "no ospf dead-interval",
       NO_STR
       "OSPF interface commands\n"
       "Interval after which a neighbor is declared dead\n")

DEFUN (ip_ospf_hello_interval,
       ip_ospf_hello_interval_addr_cmd,
       "ip ospf hello-interval <1-65535> A.B.C.D",
       "IP Information\n"
       "OSPF interface commands\n"
       "Time between HELLO packets\n"
       "Seconds\n"
       "Address of interface")
{
  struct interface *ifp = vty->index;
  u_int32_t seconds;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
      
  params = IF_DEF_PARAMS (ifp);

  seconds = strtol (argv[0], NULL, 10);
  
  /* HelloInterval range is <1-65535>. */
  if (seconds < 1 || seconds > 65535)
    {
      vty_out (vty, "Hello Interval is invalid%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  if (argc == 2)
    {
      ret = inet_aton(argv[1], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_get_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }

  SET_IF_PARAM (params, v_hello);
  params->v_hello = seconds;

  return CMD_SUCCESS;
}

ALIAS (ip_ospf_hello_interval,
       ip_ospf_hello_interval_cmd,
       "ip ospf hello-interval <1-65535>",
       "IP Information\n"
       "OSPF interface commands\n"
       "Time between HELLO packets\n"
       "Seconds\n")

ALIAS (ip_ospf_hello_interval,
       ospf_hello_interval_cmd,
       "ospf hello-interval <1-65535>",
       "OSPF interface commands\n"
       "Time between HELLO packets\n"
       "Seconds\n")

DEFUN (no_ip_ospf_hello_interval,
       no_ip_ospf_hello_interval_addr_cmd,
       "no ip ospf hello-interval A.B.C.D",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Time between HELLO packets\n"
       "Address of interface")
{
  struct interface *ifp = vty->index;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
  
  ifp = vty->index;
  params = IF_DEF_PARAMS (ifp);

  if (argc == 1)
    {
      ret = inet_aton(argv[0], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_lookup_if_params (ifp, addr);
      if (params == NULL)
	return CMD_SUCCESS;
    }

  UNSET_IF_PARAM (params, v_hello);
  params->v_hello = OSPF_HELLO_INTERVAL_DEFAULT;

  if (params != IF_DEF_PARAMS (ifp))
    {
      ospf_free_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }

  return CMD_SUCCESS;
}

ALIAS (no_ip_ospf_hello_interval,
       no_ip_ospf_hello_interval_cmd,
       "no ip ospf hello-interval",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Time between HELLO packets\n")

ALIAS (no_ip_ospf_hello_interval,
       no_ospf_hello_interval_cmd,
       "no ospf hello-interval",
       NO_STR
       "OSPF interface commands\n"
       "Time between HELLO packets\n")

DEFUN (ip_ospf_network,
       ip_ospf_network_cmd,
       "ip ospf network (broadcast|non-broadcast|point-to-multipoint|point-to-point)",
       "IP Information\n"
       "OSPF interface commands\n"
       "Network type\n"
       "Specify OSPF broadcast multi-access network\n"
       "Specify OSPF NBMA network\n"
       "Specify OSPF point-to-multipoint network\n"
       "Specify OSPF point-to-point network\n")
{
  struct interface *ifp = vty->index;
  int old_type = IF_DEF_PARAMS (ifp)->type;
  struct route_node *rn;
  
  if (strncmp (argv[0], "b", 1) == 0)
    IF_DEF_PARAMS (ifp)->type = OSPF_IFTYPE_BROADCAST;
  else if (strncmp (argv[0], "n", 1) == 0)
    IF_DEF_PARAMS (ifp)->type = OSPF_IFTYPE_NBMA;
  else if (strncmp (argv[0], "point-to-m", 10) == 0)
    IF_DEF_PARAMS (ifp)->type = OSPF_IFTYPE_POINTOMULTIPOINT;
  else if (strncmp (argv[0], "point-to-p", 10) == 0)
    IF_DEF_PARAMS (ifp)->type = OSPF_IFTYPE_POINTOPOINT;

  if (IF_DEF_PARAMS (ifp)->type == old_type)
    return CMD_SUCCESS;

  SET_IF_PARAM (IF_DEF_PARAMS (ifp), type);

  for (rn = route_top (IF_OIFS (ifp)); rn; rn = route_next (rn))
    {
      struct ospf_interface *oi = rn->info;

      if (!oi)
	continue;
      
      oi->type = IF_DEF_PARAMS (ifp)->type;
      
      if (oi->state > ISM_Down)
	{
	  OSPF_ISM_EVENT_EXECUTE (oi, ISM_InterfaceDown);
	  OSPF_ISM_EVENT_EXECUTE (oi, ISM_InterfaceUp);
	}
    }

  return CMD_SUCCESS;
}

ALIAS (ip_ospf_network,
       ospf_network_cmd,
       "ospf network (broadcast|non-broadcast|point-to-multipoint|point-to-point)",
       "OSPF interface commands\n"
       "Network type\n"
       "Specify OSPF broadcast multi-access network\n"
       "Specify OSPF NBMA network\n"
       "Specify OSPF point-to-multipoint network\n"
       "Specify OSPF point-to-point network\n")

DEFUN (no_ip_ospf_network,
       no_ip_ospf_network_cmd,
       "no ip ospf network",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Network type\n")
{
  struct interface *ifp = vty->index;
  int old_type = IF_DEF_PARAMS (ifp)->type;
  struct route_node *rn;

  IF_DEF_PARAMS (ifp)->type = ospf_default_iftype(ifp);

  if (IF_DEF_PARAMS (ifp)->type == old_type)
    return CMD_SUCCESS;

  for (rn = route_top (IF_OIFS (ifp)); rn; rn = route_next (rn))
    {
      struct ospf_interface *oi = rn->info;

      if (!oi)
	continue;
      
      oi->type = IF_DEF_PARAMS (ifp)->type;
      
      if (oi->state > ISM_Down)
	{
	  OSPF_ISM_EVENT_EXECUTE (oi, ISM_InterfaceDown);
	  OSPF_ISM_EVENT_EXECUTE (oi, ISM_InterfaceUp);
	}
    }

  return CMD_SUCCESS;
}

ALIAS (no_ip_ospf_network,
       no_ospf_network_cmd,
       "no ospf network",
       NO_STR
       "OSPF interface commands\n"
       "Network type\n")

DEFUN (ip_ospf_priority,
       ip_ospf_priority_addr_cmd,
       "ip ospf priority <0-255> A.B.C.D",
       "IP Information\n"
       "OSPF interface commands\n"
       "Router priority\n"
       "Priority\n"
       "Address of interface")
{
  struct interface *ifp = vty->index;
  u_int32_t priority;
  struct route_node *rn;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
      
  params = IF_DEF_PARAMS (ifp);

  priority = strtol (argv[0], NULL, 10);
  
  /* Router Priority range is <0-255>. */
  if (priority < 0 || priority > 255)
    {
      vty_out (vty, "Router Priority is invalid%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  if (argc == 2)
    {
      ret = inet_aton(argv[1], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_get_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }
  
  SET_IF_PARAM (params, priority);
  params->priority = priority;

  for (rn = route_top (IF_OIFS (ifp)); rn; rn = route_next (rn))
    {
      struct ospf_interface *oi = rn->info;
      
      if (!oi)
	continue;
      

      if (PRIORITY (oi) != OSPF_IF_PARAM (oi, priority))
	{
	  PRIORITY (oi) = OSPF_IF_PARAM (oi, priority);
	  OSPF_ISM_EVENT_SCHEDULE (oi, ISM_NeighborChange);
	}
    }
  
  return CMD_SUCCESS;
}

ALIAS (ip_ospf_priority,
       ip_ospf_priority_cmd,
       "ip ospf priority <0-255>",
       "IP Information\n"
       "OSPF interface commands\n"
       "Router priority\n"
       "Priority\n")

ALIAS (ip_ospf_priority,
       ospf_priority_cmd,
       "ospf priority <0-255>",
       "OSPF interface commands\n"
       "Router priority\n"
       "Priority\n")

DEFUN (no_ip_ospf_priority,
       no_ip_ospf_priority_addr_cmd,
       "no ip ospf priority A.B.C.D",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Router priority\n"
       "Address of interface")
{
  struct interface *ifp = vty->index;
  struct route_node *rn;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
  
  ifp = vty->index;
  params = IF_DEF_PARAMS (ifp);

  if (argc == 1)
    {
      ret = inet_aton(argv[0], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_lookup_if_params (ifp, addr);
      if (params == NULL)
	return CMD_SUCCESS;
    }

  UNSET_IF_PARAM (params, priority);
  params->priority = OSPF_ROUTER_PRIORITY_DEFAULT;

  if (params != IF_DEF_PARAMS (ifp))
    {
      ospf_free_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }
  
  for (rn = route_top (IF_OIFS (ifp)); rn; rn = route_next (rn))
    {
      struct ospf_interface *oi = rn->info;
      
      if (!oi)
	continue;
      
      
      if (PRIORITY (oi) != OSPF_IF_PARAM (oi, priority))
	{
	  PRIORITY (oi) = OSPF_IF_PARAM (oi, priority);
	  OSPF_ISM_EVENT_SCHEDULE (oi, ISM_NeighborChange);
	}
    }
  
  return CMD_SUCCESS;
}

ALIAS (no_ip_ospf_priority,
       no_ip_ospf_priority_cmd,
       "no ip ospf priority",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Router priority\n")

ALIAS (no_ip_ospf_priority,
       no_ospf_priority_cmd,
       "no ospf priority",
       NO_STR
       "OSPF interface commands\n"
       "Router priority\n")

DEFUN (ip_ospf_retransmit_interval,
       ip_ospf_retransmit_interval_addr_cmd,
       "ip ospf retransmit-interval <3-65535> A.B.C.D",
       "IP Information\n"
       "OSPF interface commands\n"
       "Time between retransmitting lost link state advertisements\n"
       "Seconds\n"
       "Address of interface")
{
  struct interface *ifp = vty->index;
  u_int32_t seconds;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
      
  params = IF_DEF_PARAMS (ifp);
  seconds = strtol (argv[0], NULL, 10);

  /* Retransmit Interval range is <3-65535>. */
  if (seconds < 3 || seconds > 65535)
    {
      vty_out (vty, "Retransmit Interval is invalid%s", VTY_NEWLINE);
      return CMD_WARNING;
    }


  if (argc == 2)
    {
      ret = inet_aton(argv[1], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_get_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }

  SET_IF_PARAM (params, retransmit_interval);
  params->retransmit_interval = seconds;

  return CMD_SUCCESS;
}

ALIAS (ip_ospf_retransmit_interval,
       ip_ospf_retransmit_interval_cmd,
       "ip ospf retransmit-interval <3-65535>",
       "IP Information\n"
       "OSPF interface commands\n"
       "Time between retransmitting lost link state advertisements\n"
       "Seconds\n")

ALIAS (ip_ospf_retransmit_interval,
       ospf_retransmit_interval_cmd,
       "ospf retransmit-interval <3-65535>",
       "OSPF interface commands\n"
       "Time between retransmitting lost link state advertisements\n"
       "Seconds\n")

DEFUN (no_ip_ospf_retransmit_interval,
       no_ip_ospf_retransmit_interval_addr_cmd,
       "no ip ospf retransmit-interval A.B.C.D",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Time between retransmitting lost link state advertisements\n"
       "Address of interface")
{
  struct interface *ifp = vty->index;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
  
  ifp = vty->index;
  params = IF_DEF_PARAMS (ifp);

  if (argc == 1)
    {
      ret = inet_aton(argv[0], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_lookup_if_params (ifp, addr);
      if (params == NULL)
	return CMD_SUCCESS;
    }

  UNSET_IF_PARAM (params, retransmit_interval);
  params->retransmit_interval = OSPF_RETRANSMIT_INTERVAL_DEFAULT;

  if (params != IF_DEF_PARAMS (ifp))
    {
      ospf_free_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }

  return CMD_SUCCESS;
}

ALIAS (no_ip_ospf_retransmit_interval,
       no_ip_ospf_retransmit_interval_cmd,
       "no ip ospf retransmit-interval",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Time between retransmitting lost link state advertisements\n")

ALIAS (no_ip_ospf_retransmit_interval,
       no_ospf_retransmit_interval_cmd,
       "no ospf retransmit-interval",
       NO_STR
       "OSPF interface commands\n"
       "Time between retransmitting lost link state advertisements\n")

DEFUN (ip_ospf_transmit_delay,
       ip_ospf_transmit_delay_addr_cmd,
       "ip ospf transmit-delay <1-65535> A.B.C.D",
       "IP Information\n"
       "OSPF interface commands\n"
       "Link state transmit delay\n"
       "Seconds\n"
       "Address of interface")
{
  struct interface *ifp = vty->index;
  u_int32_t seconds;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
      
  params = IF_DEF_PARAMS (ifp);
  seconds = strtol (argv[0], NULL, 10);

  /* Transmit Delay range is <1-65535>. */
  if (seconds < 1 || seconds > 65535)
    {
      vty_out (vty, "Transmit Delay is invalid%s", VTY_NEWLINE);
      return CMD_WARNING;
    }

  if (argc == 2)
    {
      ret = inet_aton(argv[1], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_get_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }

  SET_IF_PARAM (params, transmit_delay); 
  params->transmit_delay = seconds;

  return CMD_SUCCESS;
}

ALIAS (ip_ospf_transmit_delay,
       ip_ospf_transmit_delay_cmd,
       "ip ospf transmit-delay <1-65535>",
       "IP Information\n"
       "OSPF interface commands\n"
       "Link state transmit delay\n"
       "Seconds\n")

ALIAS (ip_ospf_transmit_delay,
       ospf_transmit_delay_cmd,
       "ospf transmit-delay <1-65535>",
       "OSPF interface commands\n"
       "Link state transmit delay\n"
       "Seconds\n")

DEFUN (no_ip_ospf_transmit_delay,
       no_ip_ospf_transmit_delay_addr_cmd,
       "no ip ospf transmit-delay A.B.C.D",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Link state transmit delay\n"
       "Address of interface")
{
  struct interface *ifp = vty->index;
  struct in_addr addr;
  int ret;
  struct ospf_if_params *params;
  
  ifp = vty->index;
  params = IF_DEF_PARAMS (ifp);

  if (argc == 1)
    {
      ret = inet_aton(argv[0], &addr);
      if (!ret)
	{
	  vty_out (vty, "Please specify interface address by A.B.C.D%s",
		   VTY_NEWLINE);
	  return CMD_WARNING;
	}

      params = ospf_lookup_if_params (ifp, addr);
      if (params == NULL)
	return CMD_SUCCESS;
    }

  UNSET_IF_PARAM (params, transmit_delay);
  params->transmit_delay = OSPF_TRANSMIT_DELAY_DEFAULT;

  if (params != IF_DEF_PARAMS (ifp))
    {
      ospf_free_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }

  return CMD_SUCCESS;
}

ALIAS (no_ip_ospf_transmit_delay,
       no_ip_ospf_transmit_delay_cmd,
       "no ip ospf transmit-delay",
       NO_STR
       "IP Information\n"
       "OSPF interface commands\n"
       "Link state transmit delay\n")

ALIAS (no_ip_ospf_transmit_delay,
       no_ospf_transmit_delay_cmd,
       "no ospf transmit-delay",
       NO_STR
       "OSPF interface commands\n"
       "Link state transmit delay\n")


DEFUN (ospf_redistribute_source_metric_type,
       ospf_redistribute_source_metric_type_routemap_cmd,
       "redistribute " QUAGGA_REDIST_STR_OSPFD 
         " metric <0-16777214> metric-type (1|2) route-map WORD",
       REDIST_STR
       QUAGGA_REDIST_HELP_STR_OSPFD
       "Metric for redistributed routes\n"
       "OSPF default metric\n"
       "OSPF exterior metric type for redistributed routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n"
       "Route map reference\n"
       "Pointer to route-map entries\n")
{
  zlog_debug("in func reditribute 2,0");
  struct ospf *ospf = vty->index;
  int source;
  int type = -1;
  int metric = -1;
  
  /* Get distribute source. */
  source = proto_redistnum(AFI_IP, argv[0]);
  if (source < 0 || source == ZEBRA_ROUTE_OSPF)
    return CMD_WARNING;

  /* Get metric value. */
  if (argc >= 2)
    if (!str2metric (argv[1], &metric))
      return CMD_WARNING;

  /* Get metric type. */
  if (argc >= 3)
    if (!str2metric_type (argv[2], &type))
      return CMD_WARNING;

  if (argc == 4)
    ospf_routemap_set (ospf, source, argv[3]);
  else
    ospf_routemap_unset (ospf, source);
  zlog_debug("in func redistribute 2,type=%d",type);
  return ospf_redistribute_set (ospf, source, type, metric);
}

ALIAS (ospf_redistribute_source_metric_type,
       ospf_redistribute_source_metric_type_cmd,
       "redistribute " QUAGGA_REDIST_STR_OSPFD 
       " metric <0-16777214> metric-type (1|2)",  //type 2 dont accumulate distance, type 1 accumulate distance when flood 
       REDIST_STR
       QUAGGA_REDIST_HELP_STR_OSPFD
       "Metric for redistributed routes\n"
       "OSPF default metric\n"
       "OSPF exterior metric type for redistributed routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n")

ALIAS (ospf_redistribute_source_metric_type,
       ospf_redistribute_source_metric_cmd,
       "redistribute " QUAGGA_REDIST_STR_OSPFD " metric <0-16777214>",
       REDIST_STR
       QUAGGA_REDIST_HELP_STR_OSPFD
       "Metric for redistributed routes\n"
       "OSPF default metric\n")

DEFUN (ospf_redistribute_source_type_metric,
       ospf_redistribute_source_type_metric_routemap_cmd,
       "redistribute " QUAGGA_REDIST_STR_OSPFD 
         " metric-type (1|2) metric <0-16777214> route-map WORD",
       REDIST_STR
       QUAGGA_REDIST_HELP_STR_OSPFD
       "OSPF exterior metric type for redistributed routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n"
       "Metric for redistributed routes\n"
       "OSPF default metric\n"
       "Route map reference\n"
       "Pointer to route-map entries\n")
{
  zlog_debug("in func reditribute 1,0");
  struct ospf *ospf = vty->index;
  int source;
  int type = -1;
  int metric = -1;
  zlog_debug("in func reditribute 1,1");
  /* Get distribute source. */
  source = proto_redistnum(AFI_IP, argv[0]);
  if (source < 0 || source == ZEBRA_ROUTE_OSPF)
    return CMD_WARNING;
  zlog_debug("in func reditribute 1,2");
  /* Get metric value. */
  if (argc >= 2)
    if (!str2metric_type (argv[1], &type))
      return CMD_WARNING;
  zlog_debug("in func reditribute 1,3");
  /* Get metric type. */
  if (argc >= 3)
    if (!str2metric (argv[2], &metric))
      return CMD_WARNING;
  zlog_debug("in func reditribute 1,4");
  if (argc == 4)
    ospf_routemap_set (ospf, source, argv[3]);
  else
    ospf_routemap_unset (ospf, source);

  return ospf_redistribute_set (ospf, source, type, metric);
}

ALIAS (ospf_redistribute_source_type_metric,
       ospf_redistribute_source_type_metric_cmd,
       "redistribute " QUAGGA_REDIST_STR_OSPFD 
         " metric-type (1|2) metric <0-16777214>",
       REDIST_STR
       QUAGGA_REDIST_HELP_STR_OSPFD
       "OSPF exterior metric type for redistributed routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n"
       "Metric for redistributed routes\n"
       "OSPF default metric\n")

ALIAS (ospf_redistribute_source_type_metric,
       ospf_redistribute_source_type_cmd,
       "redistribute " QUAGGA_REDIST_STR_OSPFD " metric-type (1|2)",
       REDIST_STR
       QUAGGA_REDIST_HELP_STR_OSPFD
       "OSPF exterior metric type for redistributed routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n")

ALIAS (ospf_redistribute_source_type_metric,
       ospf_redistribute_source_cmd,
       "redistribute " QUAGGA_REDIST_STR_OSPFD,
       REDIST_STR
       QUAGGA_REDIST_HELP_STR_OSPFD)

DEFUN (ospf_redistribute_source_metric_routemap,
       ospf_redistribute_source_metric_routemap_cmd,
       "redistribute " QUAGGA_REDIST_STR_OSPFD 
         " metric <0-16777214> route-map WORD",
       REDIST_STR
       QUAGGA_REDIST_HELP_STR_OSPFD
       "Metric for redistributed routes\n"
       "OSPF default metric\n"
       "Route map reference\n"
       "Pointer to route-map entries\n")
{
  struct ospf *ospf = vty->index;
  int source;
  int metric = -1;

  /* Get distribute source. */
  source = proto_redistnum(AFI_IP, argv[0]);
  if (source < 0 || source == ZEBRA_ROUTE_OSPF)
    return CMD_WARNING;

  /* Get metric value. */
  if (argc >= 2)
    if (!str2metric (argv[1], &metric))
      return CMD_WARNING;

  if (argc == 3)
    ospf_routemap_set (ospf, source, argv[2]);
  else
    ospf_routemap_unset (ospf, source);
  
  return ospf_redistribute_set (ospf, source, -1, metric);
}

DEFUN (ospf_redistribute_source_type_routemap,
       ospf_redistribute_source_type_routemap_cmd,
       "redistribute " QUAGGA_REDIST_STR_OSPFD 
         " metric-type (1|2) route-map WORD",
       REDIST_STR
       QUAGGA_REDIST_HELP_STR_OSPFD
       "OSPF exterior metric type for redistributed routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n"
       "Route map reference\n"
       "Pointer to route-map entries\n")
{
  struct ospf *ospf = vty->index;
  int source;
  int type = -1;

  /* Get distribute source. */
  source = proto_redistnum(AFI_IP, argv[0]);
  if (source < 0 || source == ZEBRA_ROUTE_OSPF)
    return CMD_WARNING;

  /* Get metric value. */
  if (argc >= 2)
    if (!str2metric_type (argv[1], &type))
      return CMD_WARNING;

  if (argc == 3)
    ospf_routemap_set (ospf, source, argv[2]);
  else
    ospf_routemap_unset (ospf, source); 

  return ospf_redistribute_set (ospf, source, type, -1);
}

DEFUN (ospf_redistribute_source_routemap,
       ospf_redistribute_source_routemap_cmd,
       "redistribute " QUAGGA_REDIST_STR_OSPFD " route-map WORD",
       REDIST_STR
       QUAGGA_REDIST_HELP_STR_OSPFD
       "Route map reference\n"
       "Pointer to route-map entries\n")
{
  struct ospf *ospf = vty->index;
  int source;

  /* Get distribute source. */
  source = proto_redistnum(AFI_IP, argv[0]);
  if (source < 0 || source == ZEBRA_ROUTE_OSPF)
    return CMD_WARNING;

  if (argc == 2)
    ospf_routemap_set (ospf, source, argv[1]);
  else
    ospf_routemap_unset (ospf, source);

  return ospf_redistribute_set (ospf, source, -1, -1);
}

DEFUN (no_ospf_redistribute_source,
       no_ospf_redistribute_source_cmd,
       "no redistribute " QUAGGA_REDIST_STR_OSPFD,
       NO_STR
       REDIST_STR
       QUAGGA_REDIST_HELP_STR_OSPFD)
{
  struct ospf *ospf = vty->index;
  int source;
  zlog_debug("in func no redistribute");
  source = proto_redistnum(AFI_IP, argv[0]);
  if (source < 0 || source == ZEBRA_ROUTE_OSPF)
    return CMD_WARNING;

  ospf_routemap_unset (ospf, source);
  return ospf_redistribute_unset (ospf, source);
}

DEFUN (ospf_distribute_list_out,
       ospf_distribute_list_out_cmd,
       "distribute-list WORD out " QUAGGA_REDIST_STR_OSPFD,
       "Filter networks in routing updates\n"
       "Access-list name\n"
       OUT_STR
       QUAGGA_REDIST_HELP_STR_OSPFD)
{
  struct ospf *ospf = vty->index;
  int source;

  /* Get distribute source. */
  source = proto_redistnum(AFI_IP, argv[0]);
  if (source < 0 || source == ZEBRA_ROUTE_OSPF)
    return CMD_WARNING;

  return ospf_distribute_list_out_set (ospf, source, argv[0]);
}

DEFUN (no_ospf_distribute_list_out,
       no_ospf_distribute_list_out_cmd,
       "no distribute-list WORD out " QUAGGA_REDIST_STR_OSPFD,
       NO_STR
       "Filter networks in routing updates\n"
       "Access-list name\n"
       OUT_STR
       QUAGGA_REDIST_HELP_STR_OSPFD)
{
  struct ospf *ospf = vty->index;
  int source;

  source = proto_redistnum(AFI_IP, argv[0]);
  if (source < 0 || source == ZEBRA_ROUTE_OSPF)
    return CMD_WARNING;

  return ospf_distribute_list_out_unset (ospf, source, argv[0]);
}

/* Default information originate. */
DEFUN (ospf_default_information_originate_metric_type_routemap,
       ospf_default_information_originate_metric_type_routemap_cmd,
       "default-information originate metric <0-16777214> metric-type (1|2) route-map WORD",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "OSPF default metric\n"
       "OSPF metric\n"
       "OSPF metric type for default routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n"
       "Route map reference\n"
       "Pointer to route-map entries\n")
{
  struct ospf *ospf = vty->index;
  int type = -1;
  int metric = -1;

  /* Get metric value. */
  if (argc >= 1)
    if (!str2metric (argv[0], &metric))
      return CMD_WARNING;

  /* Get metric type. */
  if (argc >= 2)
    if (!str2metric_type (argv[1], &type))
      return CMD_WARNING;

  if (argc == 3)
    ospf_routemap_set (ospf, DEFAULT_ROUTE, argv[2]);
  else
    ospf_routemap_unset (ospf, DEFAULT_ROUTE);

  return ospf_redistribute_default_set (ospf, DEFAULT_ORIGINATE_ZEBRA,
					type, metric);
}

ALIAS (ospf_default_information_originate_metric_type_routemap,
       ospf_default_information_originate_metric_type_cmd,
       "default-information originate metric <0-16777214> metric-type (1|2)",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "OSPF default metric\n"
       "OSPF metric\n"
       "OSPF metric type for default routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n")

ALIAS (ospf_default_information_originate_metric_type_routemap,
       ospf_default_information_originate_metric_cmd,
       "default-information originate metric <0-16777214>",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "OSPF default metric\n"
       "OSPF metric\n")

ALIAS (ospf_default_information_originate_metric_type_routemap,
       ospf_default_information_originate_cmd,
       "default-information originate",
       "Control distribution of default information\n"
       "Distribute a default route\n")

/* Default information originate. */
DEFUN (ospf_default_information_originate_metric_routemap,
       ospf_default_information_originate_metric_routemap_cmd,
       "default-information originate metric <0-16777214> route-map WORD",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "OSPF default metric\n"
       "OSPF metric\n"
       "Route map reference\n"
       "Pointer to route-map entries\n")
{
  struct ospf *ospf = vty->index;
  int metric = -1;

  /* Get metric value. */
  if (argc >= 1)
    if (!str2metric (argv[0], &metric))
      return CMD_WARNING;

  if (argc == 2)
    ospf_routemap_set (ospf, DEFAULT_ROUTE, argv[1]);
  else
    ospf_routemap_unset (ospf, DEFAULT_ROUTE);

  return ospf_redistribute_default_set (ospf, DEFAULT_ORIGINATE_ZEBRA,
					-1, metric);
}

/* Default information originate. */
DEFUN (ospf_default_information_originate_routemap,
       ospf_default_information_originate_routemap_cmd,
       "default-information originate route-map WORD",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "Route map reference\n"
       "Pointer to route-map entries\n")
{
  struct ospf *ospf = vty->index;

  if (argc == 1)
    ospf_routemap_set (ospf, DEFAULT_ROUTE, argv[0]);
  else
    ospf_routemap_unset (ospf, DEFAULT_ROUTE);

  return ospf_redistribute_default_set (ospf, DEFAULT_ORIGINATE_ZEBRA, -1, -1);
}

DEFUN (ospf_default_information_originate_type_metric_routemap,
       ospf_default_information_originate_type_metric_routemap_cmd,
       "default-information originate metric-type (1|2) metric <0-16777214> route-map WORD",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "OSPF metric type for default routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n"
       "OSPF default metric\n"
       "OSPF metric\n"
       "Route map reference\n"
       "Pointer to route-map entries\n")
{
  struct ospf *ospf = vty->index;
  int type = -1;
  int metric = -1;

  /* Get metric type. */
  if (argc >= 1)
    if (!str2metric_type (argv[0], &type))
      return CMD_WARNING;

  /* Get metric value. */
  if (argc >= 2)
    if (!str2metric (argv[1], &metric))
      return CMD_WARNING;

  if (argc == 3)
    ospf_routemap_set (ospf, DEFAULT_ROUTE, argv[2]);
  else
    ospf_routemap_unset (ospf, DEFAULT_ROUTE);

  return ospf_redistribute_default_set (ospf, DEFAULT_ORIGINATE_ZEBRA,
					type, metric);
}

ALIAS (ospf_default_information_originate_type_metric_routemap,
       ospf_default_information_originate_type_metric_cmd,
       "default-information originate metric-type (1|2) metric <0-16777214>",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "OSPF metric type for default routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n"
       "OSPF default metric\n"
       "OSPF metric\n")

ALIAS (ospf_default_information_originate_type_metric_routemap,
       ospf_default_information_originate_type_cmd,
       "default-information originate metric-type (1|2)",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "OSPF metric type for default routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n")

DEFUN (ospf_default_information_originate_type_routemap,
       ospf_default_information_originate_type_routemap_cmd,
       "default-information originate metric-type (1|2) route-map WORD",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "OSPF metric type for default routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n"
       "Route map reference\n"
       "Pointer to route-map entries\n")
{
  struct ospf *ospf = vty->index;
  int type = -1;

  /* Get metric type. */
  if (argc >= 1)
    if (!str2metric_type (argv[0], &type))
      return CMD_WARNING;

  if (argc == 2)
    ospf_routemap_set (ospf, DEFAULT_ROUTE, argv[1]);
  else
    ospf_routemap_unset (ospf, DEFAULT_ROUTE);

  return ospf_redistribute_default_set (ospf, DEFAULT_ORIGINATE_ZEBRA,
					type, -1);
}

DEFUN (ospf_default_information_originate_always_metric_type_routemap,
       ospf_default_information_originate_always_metric_type_routemap_cmd,
       "default-information originate always metric <0-16777214> metric-type (1|2) route-map WORD",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "Always advertise default route\n"
       "OSPF default metric\n"
       "OSPF metric\n"
       "OSPF metric type for default routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n"
       "Route map reference\n"
       "Pointer to route-map entries\n")
{
  struct ospf *ospf = vty->index;
  int type = -1;
  int metric = -1;

  /* Get metric value. */
  if (argc >= 1)
    if (!str2metric (argv[0], &metric))
      return CMD_WARNING;

  /* Get metric type. */
  if (argc >= 2)
    if (!str2metric_type (argv[1], &type))
      return CMD_WARNING;

  if (argc == 3)
    ospf_routemap_set (ospf, DEFAULT_ROUTE, argv[2]);
  else
    ospf_routemap_unset (ospf, DEFAULT_ROUTE);

  return ospf_redistribute_default_set (ospf, DEFAULT_ORIGINATE_ALWAYS,
					type, metric);
}

ALIAS (ospf_default_information_originate_always_metric_type_routemap,
       ospf_default_information_originate_always_metric_type_cmd,
       "default-information originate always metric <0-16777214> metric-type (1|2)",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "Always advertise default route\n"
       "OSPF default metric\n"
       "OSPF metric\n"
       "OSPF metric type for default routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n")

ALIAS (ospf_default_information_originate_always_metric_type_routemap,
       ospf_default_information_originate_always_metric_cmd,
       "default-information originate always metric <0-16777214>",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "Always advertise default route\n"
       "OSPF default metric\n"
       "OSPF metric\n"
       "OSPF metric type for default routes\n")

ALIAS (ospf_default_information_originate_always_metric_type_routemap,
       ospf_default_information_originate_always_cmd,
       "default-information originate always",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "Always advertise default route\n")

DEFUN (ospf_default_information_originate_always_metric_routemap,
       ospf_default_information_originate_always_metric_routemap_cmd,
       "default-information originate always metric <0-16777214> route-map WORD",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "Always advertise default route\n"
       "OSPF default metric\n"
       "OSPF metric\n"
       "Route map reference\n"
       "Pointer to route-map entries\n")
{
  struct ospf *ospf = vty->index;
  int metric = -1;

  /* Get metric value. */
  if (argc >= 1)
    if (!str2metric (argv[0], &metric))
      return CMD_WARNING;

  if (argc == 2)
    ospf_routemap_set (ospf, DEFAULT_ROUTE, argv[1]);
  else
    ospf_routemap_unset (ospf, DEFAULT_ROUTE);

  return ospf_redistribute_default_set (ospf, DEFAULT_ORIGINATE_ALWAYS,
					-1, metric);
}

DEFUN (ospf_default_information_originate_always_routemap,
       ospf_default_information_originate_always_routemap_cmd,
       "default-information originate always route-map WORD",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "Always advertise default route\n"
       "Route map reference\n"
       "Pointer to route-map entries\n")
{
  struct ospf *ospf = vty->index;

  if (argc == 1)
    ospf_routemap_set (ospf, DEFAULT_ROUTE, argv[0]);
  else
    ospf_routemap_unset (ospf, DEFAULT_ROUTE);

  return ospf_redistribute_default_set (ospf, DEFAULT_ORIGINATE_ALWAYS, -1, -1);
}

DEFUN (ospf_default_information_originate_always_type_metric_routemap,
       ospf_default_information_originate_always_type_metric_routemap_cmd,
       "default-information originate always metric-type (1|2) metric <0-16777214> route-map WORD",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "Always advertise default route\n"
       "OSPF metric type for default routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n"
       "OSPF default metric\n"
       "OSPF metric\n"
       "Route map reference\n"
       "Pointer to route-map entries\n")
{
  struct ospf *ospf = vty->index;
  int type = -1;
  int metric = -1;

  /* Get metric type. */
  if (argc >= 1)
    if (!str2metric_type (argv[0], &type))
      return CMD_WARNING;

  /* Get metric value. */
  if (argc >= 2)
    if (!str2metric (argv[1], &metric))
      return CMD_WARNING;

  if (argc == 3)
    ospf_routemap_set (ospf, DEFAULT_ROUTE, argv[2]);
  else
    ospf_routemap_unset (ospf, DEFAULT_ROUTE);

  return ospf_redistribute_default_set (ospf, DEFAULT_ORIGINATE_ALWAYS,
					type, metric);
}

ALIAS (ospf_default_information_originate_always_type_metric_routemap,
       ospf_default_information_originate_always_type_metric_cmd,
       "default-information originate always metric-type (1|2) metric <0-16777214>",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "Always advertise default route\n"
       "OSPF metric type for default routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n"
       "OSPF default metric\n"
       "OSPF metric\n")

ALIAS (ospf_default_information_originate_always_type_metric_routemap,
       ospf_default_information_originate_always_type_cmd,
       "default-information originate always metric-type (1|2)",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "Always advertise default route\n"
       "OSPF metric type for default routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n")

DEFUN (ospf_default_information_originate_always_type_routemap,
       ospf_default_information_originate_always_type_routemap_cmd,
       "default-information originate always metric-type (1|2) route-map WORD",
       "Control distribution of default information\n"
       "Distribute a default route\n"
       "Always advertise default route\n"
       "OSPF metric type for default routes\n"
       "Set OSPF External Type 1 metrics\n"
       "Set OSPF External Type 2 metrics\n"
       "Route map reference\n"
       "Pointer to route-map entries\n")
{
  struct ospf *ospf = vty->index;
  int type = -1;

  /* Get metric type. */
  if (argc >= 1)
    if (!str2metric_type (argv[0], &type))
      return CMD_WARNING;

  if (argc == 2)
    ospf_routemap_set (ospf, DEFAULT_ROUTE, argv[1]);
  else
    ospf_routemap_unset (ospf, DEFAULT_ROUTE);

  return ospf_redistribute_default_set (ospf, DEFAULT_ORIGINATE_ALWAYS,
					type, -1);
}

DEFUN (no_ospf_default_information_originate,
       no_ospf_default_information_originate_cmd,
       "no default-information originate",
       NO_STR
       "Control distribution of default information\n"
       "Distribute a default route\n")
{
  struct ospf *ospf = vty->index;
  struct prefix_ipv4 p;
    
  p.family = AF_INET;
  p.prefix.s_addr = 0;
  p.prefixlen = 0;

  ospf_external_lsa_flush (ospf, DEFAULT_ROUTE, &p, 0);

  if (EXTERNAL_INFO (DEFAULT_ROUTE)) {
    ospf_external_info_delete (DEFAULT_ROUTE, p);
    route_table_finish (EXTERNAL_INFO (DEFAULT_ROUTE));
    EXTERNAL_INFO (DEFAULT_ROUTE) = NULL;
  }

  ospf_routemap_unset (ospf, DEFAULT_ROUTE);
  return ospf_redistribute_default_unset (ospf);
}

DEFUN (ospf_default_metric,
       ospf_default_metric_cmd,
       "default-metric <0-16777214>",
       "Set metric of redistributed routes\n"
       "Default metric\n")
{
  struct ospf *ospf = vty->index;
  int metric = -1;

  if (!str2metric (argv[0], &metric))
    return CMD_WARNING;

  ospf->default_metric = metric;

  return CMD_SUCCESS;
}

DEFUN (no_ospf_default_metric,
       no_ospf_default_metric_cmd,
       "no default-metric",
       NO_STR
       "Set metric of redistributed routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->default_metric = -1;

  return CMD_SUCCESS;
}

ALIAS (no_ospf_default_metric,
       no_ospf_default_metric_val_cmd,
       "no default-metric <0-16777214>",
       NO_STR
       "Set metric of redistributed routes\n"
       "Default metric\n")

DEFUN (ospf_distance,
       ospf_distance_cmd,
       "distance <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_all = atoi (argv[0]);

  return CMD_SUCCESS;
}

DEFUN (no_ospf_distance,
       no_ospf_distance_cmd,
       "no distance <1-255>",
       NO_STR
       "Define an administrative distance\n"
       "OSPF Administrative distance\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_all = 0;

  return CMD_SUCCESS;
}

DEFUN (no_ospf_distance_ospf,
       no_ospf_distance_ospf_cmd,
       "no distance ospf",
       NO_STR
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "OSPF Distance\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_intra = 0;
  ospf->distance_inter = 0;
  ospf->distance_external = 0;

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_ospf_intra,
       ospf_distance_ospf_intra_cmd,
       "distance ospf intra-area <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "Intra-area routes\n"
       "Distance for intra-area routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_intra = atoi (argv[0]);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_ospf_intra_inter,
       ospf_distance_ospf_intra_inter_cmd,
       "distance ospf intra-area <1-255> inter-area <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "Intra-area routes\n"
       "Distance for intra-area routes\n"
       "Inter-area routes\n"
       "Distance for inter-area routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_intra = atoi (argv[0]);
  ospf->distance_inter = atoi (argv[1]);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_ospf_intra_external,
       ospf_distance_ospf_intra_external_cmd,
       "distance ospf intra-area <1-255> external <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "Intra-area routes\n"
       "Distance for intra-area routes\n"
       "External routes\n"
       "Distance for external routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_intra = atoi (argv[0]);
  ospf->distance_external = atoi (argv[1]);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_ospf_intra_inter_external,
       ospf_distance_ospf_intra_inter_external_cmd,
       "distance ospf intra-area <1-255> inter-area <1-255> external <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "Intra-area routes\n"
       "Distance for intra-area routes\n"
       "Inter-area routes\n"
       "Distance for inter-area routes\n"
       "External routes\n"
       "Distance for external routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_intra = atoi (argv[0]);
  ospf->distance_inter = atoi (argv[1]);
  ospf->distance_external = atoi (argv[2]);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_ospf_intra_external_inter,
       ospf_distance_ospf_intra_external_inter_cmd,
       "distance ospf intra-area <1-255> external <1-255> inter-area <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "Intra-area routes\n"
       "Distance for intra-area routes\n"
       "External routes\n"
       "Distance for external routes\n"
       "Inter-area routes\n"
       "Distance for inter-area routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_intra = atoi (argv[0]);
  ospf->distance_external = atoi (argv[1]);
  ospf->distance_inter = atoi (argv[2]);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_ospf_inter,
       ospf_distance_ospf_inter_cmd,
       "distance ospf inter-area <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "Inter-area routes\n"
       "Distance for inter-area routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_inter = atoi (argv[0]);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_ospf_inter_intra,
       ospf_distance_ospf_inter_intra_cmd,
       "distance ospf inter-area <1-255> intra-area <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "Inter-area routes\n"
       "Distance for inter-area routes\n"
       "Intra-area routes\n"
       "Distance for intra-area routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_inter = atoi (argv[0]);
  ospf->distance_intra = atoi (argv[1]);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_ospf_inter_external,
       ospf_distance_ospf_inter_external_cmd,
       "distance ospf inter-area <1-255> external <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "Inter-area routes\n"
       "Distance for inter-area routes\n"
       "External routes\n"
       "Distance for external routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_inter = atoi (argv[0]);
  ospf->distance_external = atoi (argv[1]);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_ospf_inter_intra_external,
       ospf_distance_ospf_inter_intra_external_cmd,
       "distance ospf inter-area <1-255> intra-area <1-255> external <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "Inter-area routes\n"
       "Distance for inter-area routes\n"
       "Intra-area routes\n"
       "Distance for intra-area routes\n"
       "External routes\n"
       "Distance for external routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_inter = atoi (argv[0]);
  ospf->distance_intra = atoi (argv[1]);
  ospf->distance_external = atoi (argv[2]);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_ospf_inter_external_intra,
       ospf_distance_ospf_inter_external_intra_cmd,
       "distance ospf inter-area <1-255> external <1-255> intra-area <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "Inter-area routes\n"
       "Distance for inter-area routes\n"
       "External routes\n"
       "Distance for external routes\n"
       "Intra-area routes\n"
       "Distance for intra-area routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_inter = atoi (argv[0]);
  ospf->distance_external = atoi (argv[1]);
  ospf->distance_intra = atoi (argv[2]);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_ospf_external,
       ospf_distance_ospf_external_cmd,
       "distance ospf external <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "External routes\n"
       "Distance for external routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_external = atoi (argv[0]);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_ospf_external_intra,
       ospf_distance_ospf_external_intra_cmd,
       "distance ospf external <1-255> intra-area <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "External routes\n"
       "Distance for external routes\n"
       "Intra-area routes\n"
       "Distance for intra-area routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_external = atoi (argv[0]);
  ospf->distance_intra = atoi (argv[1]);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_ospf_external_inter,
       ospf_distance_ospf_external_inter_cmd,
       "distance ospf external <1-255> inter-area <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "External routes\n"
       "Distance for external routes\n"
       "Inter-area routes\n"
       "Distance for inter-area routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_external = atoi (argv[0]);
  ospf->distance_inter = atoi (argv[1]);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_ospf_external_intra_inter,
       ospf_distance_ospf_external_intra_inter_cmd,
       "distance ospf external <1-255> intra-area <1-255> inter-area <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "External routes\n"
       "Distance for external routes\n"
       "Intra-area routes\n"
       "Distance for intra-area routes\n"
       "Inter-area routes\n"
       "Distance for inter-area routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_external = atoi (argv[0]);
  ospf->distance_intra = atoi (argv[1]);
  ospf->distance_inter = atoi (argv[2]);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_ospf_external_inter_intra,
       ospf_distance_ospf_external_inter_intra_cmd,
       "distance ospf external <1-255> inter-area <1-255> intra-area <1-255>",
       "Define an administrative distance\n"
       "OSPF Administrative distance\n"
       "External routes\n"
       "Distance for external routes\n"
       "Inter-area routes\n"
       "Distance for inter-area routes\n"
       "Intra-area routes\n"
       "Distance for intra-area routes\n")
{
  struct ospf *ospf = vty->index;

  ospf->distance_external = atoi (argv[0]);
  ospf->distance_inter = atoi (argv[1]);
  ospf->distance_intra = atoi (argv[2]);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_source,
       ospf_distance_source_cmd,
       "distance <1-255> A.B.C.D/M",
       "Administrative distance\n"
       "Distance value\n"
       "IP source prefix\n")
{
  struct ospf *ospf = vty->index;

  ospf_distance_set (vty, ospf, argv[0], argv[1], NULL);

  return CMD_SUCCESS;
}

DEFUN (no_ospf_distance_source,
       no_ospf_distance_source_cmd,
       "no distance <1-255> A.B.C.D/M",
       NO_STR
       "Administrative distance\n"
       "Distance value\n"
       "IP source prefix\n")
{
  struct ospf *ospf = vty->index;

  ospf_distance_unset (vty, ospf, argv[0], argv[1], NULL);

  return CMD_SUCCESS;
}

DEFUN (ospf_distance_source_access_list,
       ospf_distance_source_access_list_cmd,
       "distance <1-255> A.B.C.D/M WORD",
       "Administrative distance\n"
       "Distance value\n"
       "IP source prefix\n"
       "Access list name\n")
{
  struct ospf *ospf = vty->index;

  ospf_distance_set (vty, ospf, argv[0], argv[1], argv[2]);

  return CMD_SUCCESS;
}

DEFUN (no_ospf_distance_source_access_list,
       no_ospf_distance_source_access_list_cmd,
       "no distance <1-255> A.B.C.D/M WORD",
       NO_STR
       "Administrative distance\n"
       "Distance value\n"
       "IP source prefix\n"
       "Access list name\n")
{
  struct ospf *ospf = vty->index;

  ospf_distance_unset (vty, ospf, argv[0], argv[1], argv[2]);

  return CMD_SUCCESS;
}

DEFUN (ip_ospf_mtu_ignore,
       ip_ospf_mtu_ignore_addr_cmd,
       "ip ospf mtu-ignore A.B.C.D",
       "IP Information\n"
       "OSPF interface commands\n"
       "Disable mtu mismatch detection\n"
       "Address of interface")
{
  struct interface *ifp = vty->index;
  struct in_addr addr;
  int ret;
 	   
  struct ospf_if_params *params;
  params = IF_DEF_PARAMS (ifp);
 	 
  if (argc == 1)
    {
      ret = inet_aton(argv[0], &addr);
      if (!ret)
        {
          vty_out (vty, "Please specify interface address by A.B.C.D%s",
                  VTY_NEWLINE);
          return CMD_WARNING;
        }
      params = ospf_get_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }
  params->mtu_ignore = 1;
  if (params->mtu_ignore != OSPF_MTU_IGNORE_DEFAULT)
    SET_IF_PARAM (params, mtu_ignore);
  else 
    {
      UNSET_IF_PARAM (params, mtu_ignore);
      if (params != IF_DEF_PARAMS (ifp))
        {
          ospf_free_if_params (ifp, addr);
          ospf_if_update_params (ifp, addr);
        }
    }
  return CMD_SUCCESS;
}

ALIAS (ip_ospf_mtu_ignore,
      ip_ospf_mtu_ignore_cmd,
      "ip ospf mtu-ignore",
      "IP Information\n"
      "OSPF interface commands\n"
      "Disable mtu mismatch detection\n")

    
DEFUN (no_ip_ospf_mtu_ignore,
       no_ip_ospf_mtu_ignore_addr_cmd,
       "no ip ospf mtu-ignore A.B.C.D",
       "IP Information\n"
       "OSPF interface commands\n"
       "Disable mtu mismatch detection\n"
       "Address of interface")
{
  struct interface *ifp = vty->index;
  struct in_addr addr;
  int ret;
 	   
  struct ospf_if_params *params;
  params = IF_DEF_PARAMS (ifp);
 	 
  if (argc == 1)
    {
      ret = inet_aton(argv[0], &addr);
      if (!ret)
        {
          vty_out (vty, "Please specify interface address by A.B.C.D%s",
                  VTY_NEWLINE);
          return CMD_WARNING;
        }
      params = ospf_get_if_params (ifp, addr);
      ospf_if_update_params (ifp, addr);
    }
  params->mtu_ignore = 0;
  if (params->mtu_ignore != OSPF_MTU_IGNORE_DEFAULT)
    SET_IF_PARAM (params, mtu_ignore);
  else 
    {
      UNSET_IF_PARAM (params, mtu_ignore);
      if (params != IF_DEF_PARAMS (ifp))
        {
          ospf_free_if_params (ifp, addr);
          ospf_if_update_params (ifp, addr);
        }
    }
  return CMD_SUCCESS;
}

ALIAS (no_ip_ospf_mtu_ignore,
       no_ip_ospf_mtu_ignore_cmd,
      "no ip ospf mtu-ignore",
      "IP Information\n"
      "OSPF interface commands\n"
      "Disable mtu mismatch detection\n")

DEFUN (ospf_max_metric_router_lsa_admin,
       ospf_max_metric_router_lsa_admin_cmd,
       "max-metric router-lsa administrative",
       "OSPF maximum / infinite-distance metric\n"
       "Advertise own Router-LSA with infinite distance (stub router)\n"
       "Administratively applied, for an indefinite period\n")
{
  struct listnode *ln;
  struct ospf_area *area;
  struct ospf *ospf = vty->index;
    
  for (ALL_LIST_ELEMENTS_RO (ospf->areas, ln, area))
    {
      SET_FLAG (area->stub_router_state, OSPF_AREA_ADMIN_STUB_ROUTED);
      
      if (!CHECK_FLAG (area->stub_router_state, OSPF_AREA_IS_STUB_ROUTED))
          ospf_router_lsa_update_area (area);
    }
  return CMD_SUCCESS;
}

DEFUN (no_ospf_max_metric_router_lsa_admin,
       no_ospf_max_metric_router_lsa_admin_cmd,
       "no max-metric router-lsa administrative",
       NO_STR
       "OSPF maximum / infinite-distance metric\n"
       "Advertise own Router-LSA with infinite distance (stub router)\n"
       "Administratively applied, for an indefinite period\n")
{
  struct listnode *ln;
  struct ospf_area *area;
  struct ospf *ospf = vty->index;
    
  for (ALL_LIST_ELEMENTS_RO (ospf->areas, ln, area))
    {
      UNSET_FLAG (area->stub_router_state, OSPF_AREA_ADMIN_STUB_ROUTED);
      
      /* Don't trample on the start-up stub timer */
      if (CHECK_FLAG (area->stub_router_state, OSPF_AREA_IS_STUB_ROUTED)
          && !area->t_stub_router)
        {
          UNSET_FLAG (area->stub_router_state, OSPF_AREA_IS_STUB_ROUTED);
          ospf_router_lsa_update_area (area);
        }
    }
  return CMD_SUCCESS;
}

DEFUN (ospf_max_metric_router_lsa_startup,
       ospf_max_metric_router_lsa_startup_cmd,
       "max-metric router-lsa on-startup <5-86400>",
       "OSPF maximum / infinite-distance metric\n"
       "Advertise own Router-LSA with infinite distance (stub router)\n"
       "Automatically advertise stub Router-LSA on startup of OSPF\n"
       "Time (seconds) to advertise self as stub-router\n")
{
  unsigned int seconds;
  struct ospf *ospf = vty->index;
    
  if (argc != 1)
    {
      vty_out (vty, "%% Must supply stub-router period");
      return CMD_WARNING;
    }
  
  VTY_GET_INTEGER ("stub-router startup period", seconds, argv[0]);
  
  ospf->stub_router_startup_time = seconds;
  
  return CMD_SUCCESS;
}

DEFUN (no_ospf_max_metric_router_lsa_startup,
       no_ospf_max_metric_router_lsa_startup_cmd,
       "no max-metric router-lsa on-startup",
       NO_STR
       "OSPF maximum / infinite-distance metric\n"
       "Advertise own Router-LSA with infinite distance (stub router)\n"
       "Automatically advertise stub Router-LSA on startup of OSPF\n")
{
  struct listnode *ln;
  struct ospf_area *area;
  struct ospf *ospf = vty->index;
  
  ospf->stub_router_startup_time = OSPF_STUB_ROUTER_UNCONFIGURED;
  
  for (ALL_LIST_ELEMENTS_RO (ospf->areas, ln, area))
    {
      SET_FLAG (area->stub_router_state, OSPF_AREA_WAS_START_STUB_ROUTED);
      OSPF_TIMER_OFF (area->t_stub_router);
      
      /* Don't trample on admin stub routed */
      if (!CHECK_FLAG (area->stub_router_state, OSPF_AREA_ADMIN_STUB_ROUTED))
        {
          UNSET_FLAG (area->stub_router_state, OSPF_AREA_IS_STUB_ROUTED);
          ospf_router_lsa_update_area (area);
        }
    }
  return CMD_SUCCESS;
}

DEFUN (ospf_max_metric_router_lsa_shutdown,
       ospf_max_metric_router_lsa_shutdown_cmd,
       "max-metric router-lsa on-shutdown <5-86400>",
       "OSPF maximum / infinite-distance metric\n"
       "Advertise own Router-LSA with infinite distance (stub router)\n"
       "Advertise stub-router prior to full shutdown of OSPF\n"
       "Time (seconds) to wait till full shutdown\n")
{
  unsigned int seconds;
  struct ospf *ospf = vty->index;
    
  if (argc != 1)
    {
      vty_out (vty, "%% Must supply stub-router shutdown period");
      return CMD_WARNING;
    }
  
  VTY_GET_INTEGER ("stub-router shutdown wait period", seconds, argv[0]);
  
  ospf->stub_router_shutdown_time = seconds;
  
  return CMD_SUCCESS;
}

DEFUN (no_ospf_max_metric_router_lsa_shutdown,
       no_ospf_max_metric_router_lsa_shutdown_cmd,
       "no max-metric router-lsa on-shutdown",
       NO_STR
       "OSPF maximum / infinite-distance metric\n"
       "Advertise own Router-LSA with infinite distance (stub router)\n"
       "Advertise stub-router prior to full shutdown of OSPF\n")
{
  struct ospf *ospf = vty->index;
    
  ospf->stub_router_shutdown_time = OSPF_STUB_ROUTER_UNCONFIGURED;
  
  return CMD_SUCCESS;
}

static void
config_write_stub_router (struct vty *vty, struct ospf *ospf)
{
  struct listnode *ln;
  struct ospf_area *area;
  
  if (ospf->stub_router_startup_time != OSPF_STUB_ROUTER_UNCONFIGURED)
    vty_out (vty, " max-metric router-lsa on-startup %u%s",
             ospf->stub_router_startup_time, VTY_NEWLINE);
  if (ospf->stub_router_shutdown_time != OSPF_STUB_ROUTER_UNCONFIGURED)
    vty_out (vty, " max-metric router-lsa on-shutdown %u%s",
             ospf->stub_router_shutdown_time, VTY_NEWLINE);
  for (ALL_LIST_ELEMENTS_RO (ospf->areas, ln, area))
    {
      if (CHECK_FLAG (area->stub_router_state, OSPF_AREA_ADMIN_STUB_ROUTED))
        {
          vty_out (vty, " max-metric router-lsa administrative%s",
                   VTY_NEWLINE);
          break;
        }
    }
  return;
}

static void
show_ip_ospf_route_network (struct vty *vty, struct route_table *rt)
{
  struct route_node *rn;
  struct ospf_route *or;
  struct listnode *pnode, *pnnode;
  struct ospf_path *path;

  vty_out (vty, "============ OSPF network routing table ============%s",
	   VTY_NEWLINE);

  for (rn = route_top (rt); rn; rn = route_next (rn))
    if ((or = rn->info) != NULL)
      {
	char buf1[19];
	snprintf (buf1, 19, "%s/%d",
		  inet_ntoa (rn->p.u.prefix4), rn->p.prefixlen);

	switch (or->path_type)
	  {
	  case OSPF_PATH_INTER_AREA:
	    if (or->type == OSPF_DESTINATION_NETWORK)
	      vty_out (vty, "N IA %-18s    [%d] area: %s%s", buf1, or->cost,
		       inet_ntoa (or->u.std.area_id), VTY_NEWLINE);
	    else if (or->type == OSPF_DESTINATION_DISCARD)
	      vty_out (vty, "D IA %-18s    Discard entry%s", buf1, VTY_NEWLINE);
	    break;
	  case OSPF_PATH_INTRA_AREA:
	    vty_out (vty, "N    %-18s    [%d] area: %s%s", buf1, or->cost,
		     inet_ntoa (or->u.std.area_id), VTY_NEWLINE);
	    break;
	  default:
	    break;
	  }

        if (or->type == OSPF_DESTINATION_NETWORK)
          for (ALL_LIST_ELEMENTS (or->paths, pnode, pnnode, path))
            {
              if (if_lookup_by_index(path->ifindex))
                {
                  if (path->nexthop.s_addr == 0)
                    vty_out (vty, "%24s   directly attached to %s%s",
                             "", ifindex2ifname (path->ifindex), VTY_NEWLINE);
                  else
                    vty_out (vty, "%24s   via %s, %s%s", "",
                             inet_ntoa (path->nexthop),
			     ifindex2ifname (path->ifindex), VTY_NEWLINE);
                }
            }
      }
  vty_out (vty, "%s", VTY_NEWLINE);
}

static void
show_ip_ospf_route_router (struct vty *vty, struct route_table *rtrs)
{
  struct route_node *rn;
  struct ospf_route *or;
  struct listnode *pnode;
  struct listnode *node;
  struct ospf_path *path;

  vty_out (vty, "============ OSPF router routing table =============%s",
	   VTY_NEWLINE);
  for (rn = route_top (rtrs); rn; rn = route_next (rn))
    if (rn->info)
      {
	int flag = 0;

	vty_out (vty, "R    %-15s    ", inet_ntoa (rn->p.u.prefix4));

	for (ALL_LIST_ELEMENTS_RO ((struct list *)rn->info, node, or))
          {
            if (flag++)
          vty_out (vty, "%24s", "");

            /* Show path. */
            vty_out (vty, "%s [%d] area: %s",
                     (or->path_type == OSPF_PATH_INTER_AREA ? "IA" : "  "),
                     or->cost, inet_ntoa (or->u.std.area_id));
            /* Show flags. */
            vty_out (vty, "%s%s%s",
                     (or->u.std.flags & ROUTER_LSA_BORDER ? ", ABR" : ""),
                     (or->u.std.flags & ROUTER_LSA_EXTERNAL ? ", ASBR" : ""),
                     VTY_NEWLINE);
                  
                  for (ALL_LIST_ELEMENTS_RO (or->paths, pnode, path))
                    {
		      if (if_lookup_by_index(path->ifindex))
			{
			  if (path->nexthop.s_addr == 0)
			    vty_out (vty, "%24s   directly attached to %s%s",
				     "", ifindex2ifname (path->ifindex),
				     VTY_NEWLINE);
			  else
			    vty_out (vty, "%24s   via %s, %s%s", "",
				     inet_ntoa (path->nexthop),
				     ifindex2ifname (path->ifindex),
				     VTY_NEWLINE);
			}
                    }
          }
      }
  vty_out (vty, "%s", VTY_NEWLINE);
}

static void
show_ip_ospf_route_external (struct vty *vty, struct route_table *rt)
{
  struct route_node *rn;
  struct ospf_route *er;
  struct listnode *pnode, *pnnode;
  struct ospf_path *path;

  vty_out (vty, "============ OSPF external routing table ===========%s",
	   VTY_NEWLINE);
  for (rn = route_top (rt); rn; rn = route_next (rn))
    if ((er = rn->info) != NULL)
      {
	char buf1[19];
	snprintf (buf1, 19, "%s/%d",
		  inet_ntoa (rn->p.u.prefix4), rn->p.prefixlen);

	switch (er->path_type)
	  {
	  case OSPF_PATH_TYPE1_EXTERNAL:
	    vty_out (vty, "N E1 %-18s    [%d] tag: %u%s", buf1,
		     er->cost, er->u.ext.tag, VTY_NEWLINE);
	    break;
	  case OSPF_PATH_TYPE2_EXTERNAL:
	    vty_out (vty, "N E2 %-18s    [%d/%d] tag: %u%s", buf1, er->cost,
		     er->u.ext.type2_cost, er->u.ext.tag, VTY_NEWLINE);
	    break;
	  }

        for (ALL_LIST_ELEMENTS (er->paths, pnode, pnnode, path))
          {
            if (if_lookup_by_index(path->ifindex))
              {
                if (path->nexthop.s_addr == 0)
                  vty_out (vty, "%24s   directly attached to %s%s",
                           "", ifindex2ifname (path->ifindex), VTY_NEWLINE);
                else
                  vty_out (vty, "%24s   via %s, %s%s", "",
                           inet_ntoa (path->nexthop),
			   ifindex2ifname (path->ifindex),
                           VTY_NEWLINE);
              }
           }
        }
  vty_out (vty, "%s", VTY_NEWLINE);
}

DEFUN (show_ip_ospf_border_routers,
       show_ip_ospf_border_routers_cmd,
       "show ip ospf border-routers",
       SHOW_STR
       IP_STR
       "show all the ABR's and ASBR's\n"
       "for this area\n")
{
  struct ospf *ospf;

  if ((ospf = ospf_lookup ()) == NULL)
    {
      vty_out (vty, " OSPF Routing Process not enabled%s", VTY_NEWLINE);
      return CMD_SUCCESS;
    }

  if (ospf->new_table == NULL)
    {
      vty_out (vty, "No OSPF routing information exist%s", VTY_NEWLINE);
      return CMD_SUCCESS;
    }

  /* Show Network routes.
  show_ip_ospf_route_network (vty, ospf->new_table);   */

  /* Show Router routes. */
  show_ip_ospf_route_router (vty, ospf->new_rtrs);

  return CMD_SUCCESS;
}

DEFUN (show_ip_ospf_route,
       show_ip_ospf_route_cmd,
       "show ip ospf route",
       SHOW_STR
       IP_STR
       "OSPF information\n"
       "OSPF routing table\n")
{
  struct ospf *ospf;

  if ((ospf = ospf_lookup ()) == NULL)
    {
      vty_out (vty, " OSPF Routing Process not enabled%s", VTY_NEWLINE);
      return CMD_SUCCESS;
    }

  if (ospf->new_table == NULL)
    {
      vty_out (vty, "No OSPF routing information exist%s", VTY_NEWLINE);
      return CMD_SUCCESS;
    }

  /* Show Network routes. */
  show_ip_ospf_route_network (vty, ospf->new_table);

  /* Show Router routes. */
  show_ip_ospf_route_router (vty, ospf->new_rtrs);

  /* Show AS External routes. */
  show_ip_ospf_route_external (vty, ospf->old_external_route);

  return CMD_SUCCESS;
}


const char *ospf_abr_type_str[] = 
{
  "unknown",
  "standard",
  "ibm",
  "cisco",
  "shortcut"
};

const char *ospf_shortcut_mode_str[] = 
{
  "default",
  "enable",
  "disable"
};


static void
area_id2str (char *buf, int length, struct ospf_area *area)
{
  memset (buf, 0, length);

  if (area->format == OSPF_AREA_ID_FORMAT_ADDRESS)
    strncpy (buf, inet_ntoa (area->area_id), length);
  else
    sprintf (buf, "%lu", (unsigned long) ntohl (area->area_id.s_addr));
}


const char *ospf_int_type_str[] = 
{
  "unknown",		/* should never be used. */
  "point-to-point",
  "broadcast",
  "non-broadcast",
  "point-to-multipoint",
  "virtual-link",	/* should never be used. */
  "loopback"
};

/* Configuration write function for ospfd. */
static int
config_write_interface (struct vty *vty)
{
  struct listnode *n1, *n2;
  struct interface *ifp;
  struct crypt_key *ck;
  int write = 0;
  struct route_node *rn = NULL;
  struct ospf_if_params *params;

  for (ALL_LIST_ELEMENTS_RO (iflist, n1, ifp))
    {
      if (memcmp (ifp->name, "VLINK", 5) == 0)
	continue;

      vty_out (vty, "!%s", VTY_NEWLINE);
      vty_out (vty, "interface %s%s", ifp->name,
               VTY_NEWLINE);
      if (ifp->desc)
        vty_out (vty, " description %s%s", ifp->desc,
               VTY_NEWLINE);

      write++;

      params = IF_DEF_PARAMS (ifp);
      
      do {
	/* Interface Network print. */
	if (OSPF_IF_PARAM_CONFIGURED (params, type) &&
	    params->type != OSPF_IFTYPE_LOOPBACK)
	  {
	    if (params->type != ospf_default_iftype(ifp))
	      {
		vty_out (vty, " ip ospf network %s",
			 ospf_int_type_str[params->type]);
		if (params != IF_DEF_PARAMS (ifp))
		  vty_out (vty, " %s", inet_ntoa (rn->p.u.prefix4));
		vty_out (vty, "%s", VTY_NEWLINE);
	      }
	  }
	
	/* OSPF interface authentication print */
	if (OSPF_IF_PARAM_CONFIGURED (params, auth_type) &&
	    params->auth_type != OSPF_AUTH_NOTSET)
	  {
	    const char *auth_str;
	    
	    /* Translation tables are not that much help here due to syntax
	       of the simple option */
	    switch (params->auth_type)
	      {
		
	      case OSPF_AUTH_NULL:
		auth_str = " null";
		break;
		
	      case OSPF_AUTH_SIMPLE:
		auth_str = "";
		break;
		
	      case OSPF_AUTH_CRYPTOGRAPHIC:
		auth_str = " message-digest";
		break;
		
	      default:
		auth_str = "";
		break;
	      }
	    
	    vty_out (vty, " ip ospf authentication%s", auth_str);
	    if (params != IF_DEF_PARAMS (ifp))
	      vty_out (vty, " %s", inet_ntoa (rn->p.u.prefix4));
	    vty_out (vty, "%s", VTY_NEWLINE);
	  }

	/* Simple Authentication Password print. */
	if (OSPF_IF_PARAM_CONFIGURED (params, auth_simple) &&
	    params->auth_simple[0] != '\0')
	  {
	    vty_out (vty, " ip ospf authentication-key %s",
		     params->auth_simple);
	    if (params != IF_DEF_PARAMS (ifp))
	      vty_out (vty, " %s", inet_ntoa (rn->p.u.prefix4));
	    vty_out (vty, "%s", VTY_NEWLINE);
	  }
	
	/* Cryptographic Authentication Key print. */
	for (ALL_LIST_ELEMENTS_RO (params->auth_crypt, n2, ck))
	  {
	    vty_out (vty, " ip ospf message-digest-key %d md5 %s",
		     ck->key_id, ck->auth_key);
	    if (params != IF_DEF_PARAMS (ifp))
	      vty_out (vty, " %s", inet_ntoa (rn->p.u.prefix4));
	    vty_out (vty, "%s", VTY_NEWLINE);
	  }
	
	/* Interface Output Cost print. */
	if (OSPF_IF_PARAM_CONFIGURED (params, output_cost_cmd))
	  {
	    vty_out (vty, " ip ospf cost %u", params->output_cost_cmd);
	    if (params != IF_DEF_PARAMS (ifp))
	      vty_out (vty, " %s", inet_ntoa (rn->p.u.prefix4));
	    vty_out (vty, "%s", VTY_NEWLINE);
	  }
	
	/* Hello Interval print. */
	if (OSPF_IF_PARAM_CONFIGURED (params, v_hello) &&
	    params->v_hello != OSPF_HELLO_INTERVAL_DEFAULT)
	  {
	    vty_out (vty, " ip ospf hello-interval %u", params->v_hello);
	    if (params != IF_DEF_PARAMS (ifp))
	      vty_out (vty, " %s", inet_ntoa (rn->p.u.prefix4));
	    vty_out (vty, "%s", VTY_NEWLINE);
	  }
	
	
	/* Router Dead Interval print. */
	if (OSPF_IF_PARAM_CONFIGURED (params, v_wait) &&
	    params->v_wait != OSPF_ROUTER_DEAD_INTERVAL_DEFAULT)
	  {
	    vty_out (vty, " ip ospf dead-interval ");
	    
	    /* fast hello ? */
	    if (OSPF_IF_PARAM_CONFIGURED (params, fast_hello))
	      vty_out (vty, "minimal hello-multiplier %d",
	               params->fast_hello);
            else
              vty_out (vty, "%u", params->v_wait);
            
	    if (params != IF_DEF_PARAMS (ifp))
	      vty_out (vty, " %s", inet_ntoa (rn->p.u.prefix4));
	    vty_out (vty, "%s", VTY_NEWLINE);
	  }
	
      /* Router Priority print. */
	if (OSPF_IF_PARAM_CONFIGURED (params, priority) &&
	    params->priority != OSPF_ROUTER_PRIORITY_DEFAULT)
	  {
	    vty_out (vty, " ip ospf priority %u", params->priority);
	    if (params != IF_DEF_PARAMS (ifp))
	      vty_out (vty, " %s", inet_ntoa (rn->p.u.prefix4));
	    vty_out (vty, "%s", VTY_NEWLINE);
	  }
	
	/* Retransmit Interval print. */
	if (OSPF_IF_PARAM_CONFIGURED (params, retransmit_interval) &&
	    params->retransmit_interval != OSPF_RETRANSMIT_INTERVAL_DEFAULT)
	  {
	    vty_out (vty, " ip ospf retransmit-interval %u",
		     params->retransmit_interval);
	    if (params != IF_DEF_PARAMS (ifp))
	      vty_out (vty, " %s", inet_ntoa (rn->p.u.prefix4));
	    vty_out (vty, "%s", VTY_NEWLINE);
	  }
	
	/* Transmit Delay print. */
	if (OSPF_IF_PARAM_CONFIGURED (params, transmit_delay) &&
	    params->transmit_delay != OSPF_TRANSMIT_DELAY_DEFAULT)
	  {
	    vty_out (vty, " ip ospf transmit-delay %u", params->transmit_delay);
	    if (params != IF_DEF_PARAMS (ifp))
	      vty_out (vty, " %s", inet_ntoa (rn->p.u.prefix4));
	    vty_out (vty, "%s", VTY_NEWLINE);
	  }

    /* MTU ignore print. */
    if (OSPF_IF_PARAM_CONFIGURED (params, mtu_ignore) &&
       params->mtu_ignore != OSPF_MTU_IGNORE_DEFAULT)
      {
        if (params->mtu_ignore == 0)
          vty_out (vty, " no ip ospf mtu-ignore");
        else
          vty_out (vty, " ip ospf mtu-ignore");
        if (params != IF_DEF_PARAMS (ifp))
           vty_out (vty, " %s", inet_ntoa (rn->p.u.prefix4));
        vty_out (vty, "%s", VTY_NEWLINE);
      }


	while (1)
	  {
	    if (rn == NULL)
	      rn = route_top (IF_OIFS_PARAMS (ifp));
	    else
	      rn = route_next (rn);

	    if (rn == NULL)
	      break;
	    params = rn->info;
	    if (params != NULL)
	      break;
	  }
      } while (rn);
      
#ifdef HAVE_OPAQUE_LSA
      ospf_opaque_config_write_if (vty, ifp);
#endif /* HAVE_OPAQUE_LSA */
    }

  return write;
}

static int
config_write_network_area (struct vty *vty, struct ospf *ospf)
{
  struct route_node *rn;
  u_char buf[INET_ADDRSTRLEN];

  /* `network area' print. */
  for (rn = route_top (ospf->networks); rn; rn = route_next (rn))
    if (rn->info)
      {
	struct ospf_network *n = rn->info;

	memset (buf, 0, INET_ADDRSTRLEN);

	/* Create Area ID string by specified Area ID format. */
	if (n->format == OSPF_AREA_ID_FORMAT_ADDRESS)
	  strncpy ((char *) buf, inet_ntoa (n->area_id), INET_ADDRSTRLEN);
	else
	  sprintf ((char *) buf, "%lu", 
		   (unsigned long int) ntohl (n->area_id.s_addr));

	/* Network print. */
	vty_out (vty, " network %s/%d area %s%s",
		 inet_ntoa (rn->p.u.prefix4), rn->p.prefixlen,
		 buf, VTY_NEWLINE);
      }

  return 0;
}

static int
config_write_ospf_area (struct vty *vty, struct ospf *ospf)
{
  struct listnode *node;
  struct ospf_area *area;
  u_char buf[INET_ADDRSTRLEN];

  /* Area configuration print. */
  for (ALL_LIST_ELEMENTS_RO (ospf->areas, node, area))
    {
      struct route_node *rn1;

      area_id2str ((char *) buf, INET_ADDRSTRLEN, area);

      if (area->auth_type != OSPF_AUTH_NULL)
	{
	  if (area->auth_type == OSPF_AUTH_SIMPLE)
	    vty_out (vty, " area %s authentication%s", buf, VTY_NEWLINE);
	  else
	    vty_out (vty, " area %s authentication message-digest%s",
		     buf, VTY_NEWLINE);
	}

      if (area->shortcut_configured != OSPF_SHORTCUT_DEFAULT)
	vty_out (vty, " area %s shortcut %s%s", buf,
		 ospf_shortcut_mode_str[area->shortcut_configured],
		 VTY_NEWLINE);

      if ((area->external_routing == OSPF_AREA_STUB)
	  || (area->external_routing == OSPF_AREA_NSSA)
	  )
	{
	  if (area->external_routing == OSPF_AREA_STUB)
	    vty_out (vty, " area %s stub", buf);
	  else if (area->external_routing == OSPF_AREA_NSSA)
	    {
	      vty_out (vty, " area %s nssa", buf);
	      switch (area->NSSATranslatorRole)
	        {
	          case OSPF_NSSA_ROLE_NEVER:
	            vty_out (vty, " translate-never");
	            break;
	          case OSPF_NSSA_ROLE_ALWAYS:
	            vty_out (vty, " translate-always");
	            break;
	          case OSPF_NSSA_ROLE_CANDIDATE:
	          default:
	            vty_out (vty, " translate-candidate");
	        }
	    }

	  if (area->no_summary)
	    vty_out (vty, " no-summary");

	  vty_out (vty, "%s", VTY_NEWLINE);

	  if (area->default_cost != 1)
	    vty_out (vty, " area %s default-cost %d%s", buf, 
		     area->default_cost, VTY_NEWLINE);
	}

      for (rn1 = route_top (area->ranges); rn1; rn1 = route_next (rn1))
	if (rn1->info)
	  {
	    struct ospf_area_range *range = rn1->info;

	    vty_out (vty, " area %s range %s/%d", buf,
		     inet_ntoa (rn1->p.u.prefix4), rn1->p.prefixlen);

	    if (range->cost_config != OSPF_AREA_RANGE_COST_UNSPEC)
	      vty_out (vty, " cost %d", range->cost_config);

	    if (!CHECK_FLAG (range->flags, OSPF_AREA_RANGE_ADVERTISE))
	      vty_out (vty, " not-advertise");

	    if (CHECK_FLAG (range->flags, OSPF_AREA_RANGE_SUBSTITUTE))
	      vty_out (vty, " substitute %s/%d",
		       inet_ntoa (range->subst_addr), range->subst_masklen);

	    vty_out (vty, "%s", VTY_NEWLINE);
	  }

      if (EXPORT_NAME (area))
	vty_out (vty, " area %s export-list %s%s", buf,
		 EXPORT_NAME (area), VTY_NEWLINE);

      if (IMPORT_NAME (area))
	vty_out (vty, " area %s import-list %s%s", buf,
		 IMPORT_NAME (area), VTY_NEWLINE);

      if (PREFIX_NAME_IN (area))
	vty_out (vty, " area %s filter-list prefix %s in%s", buf,
		 PREFIX_NAME_IN (area), VTY_NEWLINE);

      if (PREFIX_NAME_OUT (area))
	vty_out (vty, " area %s filter-list prefix %s out%s", buf,
		 PREFIX_NAME_OUT (area), VTY_NEWLINE);
    }

  return 0;
}

static int
config_write_ospf_nbr_nbma (struct vty *vty, struct ospf *ospf)
{
  struct ospf_nbr_nbma *nbr_nbma;
  struct route_node *rn;

  /* Static Neighbor configuration print. */
  for (rn = route_top (ospf->nbr_nbma); rn; rn = route_next (rn))
    if ((nbr_nbma = rn->info))
      {
	vty_out (vty, " neighbor %s", inet_ntoa (nbr_nbma->addr));

	if (nbr_nbma->priority != OSPF_NEIGHBOR_PRIORITY_DEFAULT)
	  vty_out (vty, " priority %d", nbr_nbma->priority);

	if (nbr_nbma->v_poll != OSPF_POLL_INTERVAL_DEFAULT)
	  vty_out (vty, " poll-interval %d", nbr_nbma->v_poll);

	vty_out (vty, "%s", VTY_NEWLINE);
      }

  return 0;
}

static int
config_write_virtual_link (struct vty *vty, struct ospf *ospf)
{
  struct listnode *node;
  struct ospf_vl_data *vl_data;
  u_char buf[INET_ADDRSTRLEN];

  /* Virtual-Link print */
  for (ALL_LIST_ELEMENTS_RO (ospf->vlinks, node, vl_data))
    {
      struct listnode *n2;
      struct crypt_key *ck;
      struct ospf_interface *oi;

      if (vl_data != NULL)
	{
	  memset (buf, 0, INET_ADDRSTRLEN);
	  
	  if (vl_data->format == OSPF_AREA_ID_FORMAT_ADDRESS)
	    strncpy ((char *) buf, inet_ntoa (vl_data->vl_area_id), INET_ADDRSTRLEN);
	  else
	    sprintf ((char *) buf, "%lu", 
		     (unsigned long int) ntohl (vl_data->vl_area_id.s_addr));
	  oi = vl_data->vl_oi;

	  /* timers */
	  if (OSPF_IF_PARAM (oi, v_hello) != OSPF_HELLO_INTERVAL_DEFAULT ||
	      OSPF_IF_PARAM (oi, v_wait) != OSPF_ROUTER_DEAD_INTERVAL_DEFAULT ||
	      OSPF_IF_PARAM (oi, retransmit_interval) != OSPF_RETRANSMIT_INTERVAL_DEFAULT ||
	      OSPF_IF_PARAM (oi, transmit_delay) != OSPF_TRANSMIT_DELAY_DEFAULT)
	    vty_out (vty, " area %s virtual-link %s hello-interval %d retransmit-interval %d transmit-delay %d dead-interval %d%s",
		     buf,
		     inet_ntoa (vl_data->vl_peer), 
		     OSPF_IF_PARAM (oi, v_hello),
		     OSPF_IF_PARAM (oi, retransmit_interval),
		     OSPF_IF_PARAM (oi, transmit_delay),
		     OSPF_IF_PARAM (oi, v_wait),
		     VTY_NEWLINE);
	  else
	    vty_out (vty, " area %s virtual-link %s%s", buf,
		     inet_ntoa (vl_data->vl_peer), VTY_NEWLINE);
	  /* Auth key */
	  if (IF_DEF_PARAMS (vl_data->vl_oi->ifp)->auth_simple[0] != '\0')
	    vty_out (vty, " area %s virtual-link %s authentication-key %s%s",
		     buf,
		     inet_ntoa (vl_data->vl_peer),
		     IF_DEF_PARAMS (vl_data->vl_oi->ifp)->auth_simple,
		     VTY_NEWLINE);
	  /* md5 keys */
	  for (ALL_LIST_ELEMENTS_RO (IF_DEF_PARAMS (vl_data->vl_oi->ifp)->auth_crypt,
                                     n2, ck))
            vty_out (vty, " area %s virtual-link %s"
                     " message-digest-key %d md5 %s%s",
                     buf,
                     inet_ntoa (vl_data->vl_peer),
                     ck->key_id, ck->auth_key, VTY_NEWLINE);
	 
	}
    }

  return 0;
}


static int
config_write_ospf_redistribute (struct vty *vty, struct ospf *ospf)
{
  int type;

  /* redistribute print. */
  for (type = 0; type < ZEBRA_ROUTE_MAX; type++)
    if (type != zclient->redist_default && zclient->redist[type])
      {
        vty_out (vty, " redistribute %s", zebra_route_string(type));
	if (ospf->dmetric[type].value >= 0)
	  vty_out (vty, " metric %d", ospf->dmetric[type].value);
	
        if (ospf->dmetric[type].type == EXTERNAL_METRIC_TYPE_1)
	  vty_out (vty, " metric-type 1");

	if (ROUTEMAP_NAME (ospf, type))
	  vty_out (vty, " route-map %s", ROUTEMAP_NAME (ospf, type));
	
        vty_out (vty, "%s", VTY_NEWLINE);
      }

  return 0;
}

static int
config_write_ospf_default_metric (struct vty *vty, struct ospf *ospf)
{
  if (ospf->default_metric != -1)
    vty_out (vty, " default-metric %d%s", ospf->default_metric,
	     VTY_NEWLINE);
  return 0;
}

static int
config_write_ospf_distribute (struct vty *vty, struct ospf *ospf)
{
  int type;

  if (ospf)
    {
      /* distribute-list print. */
      for (type = 0; type < ZEBRA_ROUTE_MAX; type++)
	if (DISTRIBUTE_NAME (ospf, type))
	  vty_out (vty, " distribute-list %s out %s%s", 
		   DISTRIBUTE_NAME (ospf, type),
		   zebra_route_string(type), VTY_NEWLINE);

      /* default-information print. */
      if (ospf->default_originate != DEFAULT_ORIGINATE_NONE)
	{
	  vty_out (vty, " default-information originate");
	  if (ospf->default_originate == DEFAULT_ORIGINATE_ALWAYS)
	    vty_out (vty, " always");

	  if (ospf->dmetric[DEFAULT_ROUTE].value >= 0)
	    vty_out (vty, " metric %d",
		     ospf->dmetric[DEFAULT_ROUTE].value);
	  if (ospf->dmetric[DEFAULT_ROUTE].type == EXTERNAL_METRIC_TYPE_1)
	    vty_out (vty, " metric-type 1");

	  if (ROUTEMAP_NAME (ospf, DEFAULT_ROUTE))
	    vty_out (vty, " route-map %s",
		     ROUTEMAP_NAME (ospf, DEFAULT_ROUTE));
	  
	  vty_out (vty, "%s", VTY_NEWLINE);
	}

    }

  return 0;
}

static int
config_write_ospf_distance (struct vty *vty, struct ospf *ospf)
{
  struct route_node *rn;
  struct ospf_distance *odistance;

  if (ospf->distance_all)
    vty_out (vty, " distance %d%s", ospf->distance_all, VTY_NEWLINE);

  if (ospf->distance_intra 
      || ospf->distance_inter 
      || ospf->distance_external)
    {
      vty_out (vty, " distance ospf");

      if (ospf->distance_intra)
	vty_out (vty, " intra-area %d", ospf->distance_intra);
      if (ospf->distance_inter)
	vty_out (vty, " inter-area %d", ospf->distance_inter);
      if (ospf->distance_external)
	vty_out (vty, " external %d", ospf->distance_external);

      vty_out (vty, "%s", VTY_NEWLINE);
    }
  
  for (rn = route_top (ospf->distance_table); rn; rn = route_next (rn))
    if ((odistance = rn->info) != NULL)
      {
	vty_out (vty, " distance %d %s/%d %s%s", odistance->distance,
		 inet_ntoa (rn->p.u.prefix4), rn->p.prefixlen,
		 odistance->access_list ? odistance->access_list : "",
		 VTY_NEWLINE);
      }
  return 0;
}

/* OSPF configuration write function. */
static int
ospf_config_write (struct vty *vty)
{
  struct ospf *ospf;
  struct interface *ifp;
  struct ospf_interface *oi;
  struct listnode *node;
  int write = 0;

  ospf = ospf_lookup ();
  if (ospf != NULL)
    {
      /* `router ospf' print. */
      vty_out (vty, "router ospf%s", VTY_NEWLINE);

      write++;

      if (!ospf->networks)
        return write;

      /* Router ID print. */
      if (ospf->router_id_static.s_addr != 0)
        vty_out (vty, " ospf router-id %s%s",
                 inet_ntoa (ospf->router_id_static), VTY_NEWLINE);

      /* ABR type print. */
      if (ospf->abr_type != OSPF_ABR_DEFAULT)
        vty_out (vty, " ospf abr-type %s%s", 
                 ospf_abr_type_str[ospf->abr_type], VTY_NEWLINE);

      /* log-adjacency-changes flag print. */
      if (CHECK_FLAG(ospf->config, OSPF_LOG_ADJACENCY_CHANGES))
	{
	  vty_out(vty, " log-adjacency-changes");
	  if (CHECK_FLAG(ospf->config, OSPF_LOG_ADJACENCY_DETAIL))
	    vty_out(vty, " detail");
	  vty_out(vty, "%s", VTY_NEWLINE);
	}

      /* RFC1583 compatibility flag print -- Compatible with CISCO 12.1. */
      if (CHECK_FLAG (ospf->config, OSPF_RFC1583_COMPATIBLE))
	vty_out (vty, " compatible rfc1583%s", VTY_NEWLINE);

      /* auto-cost reference-bandwidth configuration.  */
      if (ospf->ref_bandwidth != OSPF_DEFAULT_REF_BANDWIDTH)
        {
          vty_out (vty, "! Important: ensure reference bandwidth "
                        "is consistent across all routers%s", VTY_NEWLINE);
          vty_out (vty, " auto-cost reference-bandwidth %d%s",
		   ospf->ref_bandwidth / 1000, VTY_NEWLINE);
        }

      /* SPF timers print. */
      if (ospf->spf_delay != OSPF_SPF_DELAY_DEFAULT ||
	  ospf->spf_holdtime != OSPF_SPF_HOLDTIME_DEFAULT ||
	  ospf->spf_max_holdtime != OSPF_SPF_MAX_HOLDTIME_DEFAULT)
	vty_out (vty, " timers throttle spf %d %d %d%s",
		 ospf->spf_delay, ospf->spf_holdtime,
		 ospf->spf_max_holdtime, VTY_NEWLINE);
      
      /* Max-metric router-lsa print */
      config_write_stub_router (vty, ospf);
      
      /* SPF refresh parameters print. */
      if (ospf->lsa_refresh_interval != OSPF_LSA_REFRESH_INTERVAL_DEFAULT)
	vty_out (vty, " refresh timer %d%s",
		 ospf->lsa_refresh_interval, VTY_NEWLINE);

      /* Redistribute information print. */
      config_write_ospf_redistribute (vty, ospf);

      /* passive-interface print. */
      if (ospf->passive_interface_default == OSPF_IF_PASSIVE)
        vty_out (vty, " passive-interface default%s", VTY_NEWLINE);
      
      for (ALL_LIST_ELEMENTS_RO (om->iflist, node, ifp))
        if (OSPF_IF_PARAM_CONFIGURED (IF_DEF_PARAMS (ifp), passive_interface)
            && IF_DEF_PARAMS (ifp)->passive_interface != 
                              ospf->passive_interface_default)
          {
            vty_out (vty, " %spassive-interface %s%s",
                     IF_DEF_PARAMS (ifp)->passive_interface ? "" : "no ",
                     ifp->name, VTY_NEWLINE);
          }
      for (ALL_LIST_ELEMENTS_RO (ospf->oiflist, node, oi))
        {
          if (!OSPF_IF_PARAM_CONFIGURED (oi->params, passive_interface))
            continue;
          if (OSPF_IF_PARAM_CONFIGURED (IF_DEF_PARAMS (oi->ifp),
                                        passive_interface))
            {
              if (oi->params->passive_interface == IF_DEF_PARAMS (oi->ifp)->passive_interface)
                continue;
            }
          else if (oi->params->passive_interface == ospf->passive_interface_default)
            continue;
          
          vty_out (vty, " %spassive-interface %s %s%s",
                   oi->params->passive_interface ? "" : "no ",
                   oi->ifp->name,
                   inet_ntoa (oi->address->u.prefix4), VTY_NEWLINE);
        }
      
      /* Network area print. */
      config_write_network_area (vty, ospf);

      /* Area config print. */
      config_write_ospf_area (vty, ospf);

      /* static neighbor print. */
      config_write_ospf_nbr_nbma (vty, ospf);

      /* Virtual-Link print. */
      config_write_virtual_link (vty, ospf);

      /* Default metric configuration.  */
      config_write_ospf_default_metric (vty, ospf);

      /* Distribute-list and default-information print. */
      config_write_ospf_distribute (vty, ospf);

      /* Distance configuration. */
      config_write_ospf_distance (vty, ospf);

#ifdef HAVE_OPAQUE_LSA
      ospf_opaque_config_write_router (vty, ospf);
#endif /* HAVE_OPAQUE_LSA */
    }

  return write;
}

DEFUN (output_lsdb,
       output_lsdb_cmd,
       "outputlsdb FILENAME",
       "output lsdb to txt\n")
{
  /*
  vty_out(vty,"this is a test,argc=%d,%s",argc,VTY_NEWLINE);

  for(int i=0;i<argc;++i){
    vty_out(vty,"%s%s",argv[i],VTY_NEWLINE);
  }
  */

  struct ospf *ospf=ospf_lookup ();
  if(ospf==NULL){
    vty_out(vty,"find ospf fail%s",VTY_NEWLINE);
    return CMD_WARNING;
  }
  vty_out(vty,"ospf_lookup_success%s",VTY_NEWLINE);
  struct route_table *rt;
  struct route_node *rn;
  struct ospf_lsa *lsa;
  struct router_lsa *rl;
  
  struct listnode *node;
  struct ospf_area *area;
  struct lsa_header *lsh;

  int i,len;
  FILE *file;
  vty_out(vty,"%s%s",argv[0],VTY_NEWLINE);
  file=fopen(argv[0],"w+");
  if(file==NULL){
    vty_out(vty,"open fail%s",VTY_NEWLINE);
    return CMD_WARNING;
  }
  for (ALL_LIST_ELEMENTS_RO (ospf->areas, node, area)){
    rt=AREA_LSDB(area,OSPF_ROUTER_LSA);
    
    for (rn = route_top ( rt ) ; rn ; rn = route_next ( rn ))
    {
      lsa=rn->info;
      if(lsa==NULL){
        continue;
      }
      else
      {
        rl=(struct router_lsa *)lsa->data;
        lsh=&rl->header;

        len=ntohs(rl->header.length)-4;

        vty_out(vty,"lsh->id=%s%s",inet_ntoa(lsh->id),VTY_NEWLINE);
        vty_out(vty,"lsh->adv_router=%s%s",inet_ntoa(lsh->adv_router),VTY_NEWLINE);

        vty_out(vty,"!,%d,%d,%d,%s,%s,%d,%d,%d%s",ntohs(lsh->ls_age),lsh->options,lsh->type,inet_ntoa(lsh->id),
                       inet_ntoa(lsh->adv_router),ntohl(lsh->ls_seqnum),ntohs(lsh->checksum),ntohs(lsh->length),VTY_NEWLINE);
        fprintf(file,"!,%d,%d,%d,%s,%s,%d,%d,%d,\n",ntohs(lsh->ls_age),lsh->options,lsh->type,inet_ntoa(lsh->id),
                      inet_ntoa(lsh->adv_router),ntohl(lsh->ls_seqnum),ntohs(lsh->checksum),ntohs(lsh->length));
        
        vty_out(vty,"@,%d,%d,%d,%d%s",(int)rl->flags,(int)rl->zero,ntohs(rl->links),lsa->phase_count,VTY_NEWLINE);
        fprintf(file,"@,%d,%d,%d,%d\n",(int)rl->flags,(int)rl->zero,ntohs(rl->links),lsa->phase_count);

        for(i = 0; i < ntohs (rl->links) && len > 0; len -= 12, i++)
        {
          //此�?�连�?输出link_id,link_data将发生�?��?的重复？因而分开输出
          vty_out(vty,"#,%d,%s,",rl->link[i].type,inet_ntoa(rl->link[i].link_id));
          vty_out(vty,"%s,%d%s",inet_ntoa(rl->link[i].link_data),ntohs(rl->link[i].metric),VTY_NEWLINE);

          fprintf(file,"#,%d,%s,",rl->link[i].type,inet_ntoa(rl->link[i].link_id));
          fprintf(file,"%s,%d,\n",inet_ntoa(rl->link[i].link_data),ntohs(rl->link[i].metric));
        }


      }
    }
    
  }
  fclose(file);

  return CMD_SUCCESS;

}

struct ospf_lsdb *vty_test_db;

void input_lsdb_sub(const char *path)
{
  DATA_INFO_STR data_info_str;

  fileToMatrix_str(path,&data_info_str);
  if(data_info_str.row_total==0)
  {
    return;
  }

  int i,j,lsa_count;

  lsa_count=0;
  for(i=0;i<data_info_str.row_total;++i)
  {
    if(data_info_str.matrix[i][0][0]=='!')
    {
      lsa_count++;
    }
    
    for(j=0;j<data_info_str.line_total[i];++j)
    {
      zlog_debug("input,matric[%d][%d]=%s",i,j,data_info_str.matrix[i][j]);
    }
    
  }

  int *startline=(int *)calloc(lsa_count,sizeof(int));
  int *linkcount=(int *)calloc(lsa_count,sizeof(int));
  j=0;
  
  for(i=0;i<data_info_str.row_total;++i)
  {
    
    if( data_info_str.matrix[i][0][0]=='!')
    {
      startline[j]=i;
      linkcount[j]=0;
      j++;
    }
    else if(data_info_str.matrix[i][0][0]=='#')
    {
      linkcount[j-1]++;    
    }
  }

  for(i=0;i<lsa_count;++i)
  {
    zlog_debug("startline=%d,countline=%d",startline[i],linkcount[i]);
  }
  zlog_debug("there is %d lsas",lsa_count);
  
  struct ospf_lsa *lsa;
  struct stream *s=NULL;
  struct lsa_header *lsah;
  struct in_addr temp_addr;
  struct router_lsa *rl;
  int links_curlsa,link_count,lsa_length;
  struct ospf *ospf=ospf_lookup ();
  links_curlsa=0;
  link_count=0;
  lsa_length=0;

  for(i=0;i<data_info_str.row_total;++i)
  {
    zlog_debug("data_info_str.line_total[%d]:%d",i,data_info_str.line_total[i]);
    if(data_info_str.matrix[i][0][0]=='!')
    {
      
      s=stream_new (OSPF_MAX_LSA_SIZE);
      lsa = ospf_lsa_new ();
      //zlog_debug("7");
      lsah=(struct lsa_header *) STREAM_DATA (s);
      lsah->ls_age=htons (OSPF_LSA_INITIAL_AGE);
      lsah->options=(u_char) atoi (data_info_str.matrix[i][2]);
      lsah->type=(u_char)atoi (data_info_str.matrix[i][3]);

      inet_aton(data_info_str.matrix[i][4],&temp_addr);
      lsah->id=temp_addr;

      inet_aton(data_info_str.matrix[i][5],&temp_addr);
      lsah->adv_router=temp_addr;

      lsah->ls_seqnum=htonl(atoi(data_info_str.matrix[i][6])+1);
      //lsah->checksum fang dao zui hou zai ji suan 
      
      lsah->length=htons(atoi(data_info_str.matrix[i][8]));
      //zlog_debug("8");
      stream_forward_endp (s, OSPF_LSA_HEADER_SIZE); 
      //zlog_debug("9");
      lsa_length=OSPF_LSA_HEADER_SIZE;

      zlog_debug("lsa header write successful");
      
    }
    else if(data_info_str.matrix[i][0][0]=='@')
    {
      rl=(struct router_lsa *) STREAM_DATA (s);
      rl->flags = (u_char) atoi(data_info_str.matrix[i][1]);
      rl->zero = (u_char) atoi(data_info_str.matrix[i][2]);
      rl->links = htons(atoi(data_info_str.matrix[i][3]));
      stream_forward_endp (s, 4);


      links_curlsa=atoi(data_info_str.matrix[i][3]);
      link_count=0;
      lsa_length+=4;
      lsa->phase_count=atoi(data_info_str.matrix[i][4]);
      lsa->links_count=links_curlsa;

      lsa->phase_matrix=(int **)calloc(links_curlsa,sizeof(int *));
      for(j=0;j<links_curlsa;++j)
      {
        lsa->phase_matrix[j]=(int *)calloc(lsa->phase_count,sizeof(int));
      }

      zlog_debug("lsa length write successful,links_curlsa=%d",links_curlsa);

    }
    else if(data_info_str.matrix[i][0][0]=='#')
    {
      //inet_aton 将转�?为网络字节序，stream put会将主机字节序调整为网络字节序，两�?�调整后抵消
      inet_aton(data_info_str.matrix[i][2],&temp_addr);
      stream_putl(s,htonl(temp_addr.s_addr));//link_id
      inet_aton(data_info_str.matrix[i][3],&temp_addr);
      stream_putl(s,htonl(temp_addr.s_addr));//link_data
      

      stream_putc (s,atoi(data_info_str.matrix[i][1]));//type
      stream_putc (s,0);//tos
      stream_putw (s,atoi(data_info_str.matrix[i][4]));//metric

      for(j=0;j<lsa->phase_count;++j)
      {
        lsa->phase_matrix[link_count][j]=atoi(data_info_str.matrix[i][j+5]);
        zlog_debug("lsa->phase_matrix[%d][%d]=%d",link_count,j,lsa->phase_matrix[link_count][j]);
      }
      
      lsa_length+=12;
      link_count++;
      zlog_debug("lsa link write successful");
      //all links have been store in stream
      if(link_count==links_curlsa)
      {
 
        zlog_debug("link full, begin install");
        
 
        //zlog_debug("lsa length: %d,stream.size:%d",lsa_length,s->size);

        lsa->data=ospf_lsa_data_new (lsa_length);
        zlog_debug("input router lsa, intstall 1");
        lsah=(struct lsa_header *) STREAM_DATA (s);
        
        zlog_debug("2");
        memcpy(lsa->data,STREAM_DATA (s),lsa_length);
        zlog_debug("3");
        
        ospf_lsa_is_self_originated(ospf,lsa);
        zlog_debug("4");
        lsah->checksum=ospf_lsa_checksum(lsah);

        lsa->area=ospf->backbone;
        lsa->lock=1;
        lsa->lsdb=vty_test_db;
        zlog_debug("5");

        ospf_lsdb_add(vty_test_db,lsa);
        stream_free(s);
        s=NULL;

        zlog_debug("6");
      }
    }
  
  }
}

DEFUN( input_lsdb,
       input_lsdb_cmd,
       "inputlsdb FILENAME",
       "input lsdb from txt\n")
{
  input_lsdb_sub(argv[0]);
  return CMD_SUCCESS;
}

void change_lsdb_sub()
{
  struct ospf *ospf=ospf_lookup ();
  struct ospf_lsdb *tmp;

  tmp=ospf->backbone->lsdb;
  ospf->backbone->lsdb=vty_test_db;
  vty_test_db=tmp;

  //modify router_lsa_self
  struct ospf_lsa *lsa,*lsa1;
  struct router_lsa *rl;
  struct route_node *rn;
  struct route_table *db;
  struct ospf_area *area;
  lsa=ospf->backbone->router_lsa_self;
  area=ospf->backbone;
  db=ospf->backbone->lsdb->type[OSPF_ROUTER_LSA].db;
  if(lsa!=NULL)
  {
    zlog_debug("lsa->lock=%d,lsa->refresh_list=%d,lsa->retransmit_count=%d",lsa->lock,lsa->refresh_list,lsa->retransmit_counter);

    ospf_ls_retransmit_delete_nbr_area (area, lsa);
    ospf_refresher_unregister_lsa (area->ospf, lsa);
    zlog_debug("free router lsa self success");
    for(rn=route_top(db);rn;rn=route_next(rn))
    {
      zlog_debug("rn->id=%x,prefixlen=%d",rn->p.u.prefix4.s_addr,rn->p.prefixlen);
      lsa1=(struct ospf_lsa *)rn->info;
      if(lsa1!=NULL)
      {
        //set lsa->lsdb=backbone
        lsa1->area=area;
        rl=(struct router_lsa *)lsa1->data;
        zlog_debug("rl->adv_router:%x,ospf->router_id:%x",rl->header.adv_router.s_addr,ospf->router_id.s_addr);
        if(rl->header.adv_router.s_addr==ospf->router_id.s_addr)
        {
          ospf->backbone->router_lsa_self=lsa1;
          break;
        }
      }
    }
  }
}


DEFUN( change_lsdb,
       change_lsdb_cmd,
       "changelsdb",
       "change lsdb backbone\n")
{
  change_lsdb_sub();
  return CMD_SUCCESS;
}

DEFUN(load_lsdb,
      load_lsdb_cmd,
      "loadlsdb",
      "load lsdb backbone\n")
{
  struct ospf *ospf=ospf_lookup ();

  struct ospf_lsa *lsa,*lsa1,*lsa_dup;

  struct route_node *rn,*rn1;
  struct route_table *db;
  struct ospf_area *area;
  zlog_debug("in func load lsdb");
  area=ospf->backbone;
  db=ospf->backbone->lsdb->type[OSPF_ROUTER_LSA].db;
  if(area==NULL || db==NULL)
  {
    return CMD_WARNING;
  }
  /*
  for(rn=route_top(db);rn;rn=route_next(rn))
  {
    zlog_debug("rn->id=%x,prefixlen=%d",rn->p.u.prefix4.s_addr,rn->p.prefixlen);
    lsa=(struct ospf_lsa *)rn->info;
    if(lsa!=NULL)
    {
      zlog_debug("before clear,lsa->lock=%d,lsa->refresh_list=%d,lsa->retransmit_count=%d",lsa->lock,lsa->refresh_list,lsa->retransmit_counter);
      for(rn1=route_top(vty_test_db->type[OSPF_ROUTER_LSA].db);rn1;rn1=route_next(rn1))
      {
        lsa1=(struct ospf_lsa *)rn1->info;
        if(lsa1!=NULL)
        {
          if(lsa1->data->id.s_addr==lsa->data->id.s_addr)
          {

          
            lsa_dup=ospf_lsa_dup(lsa1);
            lsa_dup->area=area;
            lsa_dup->lsdb=ospf->backbone->lsdb;
            //ospf_lsdb_add(ospf->backbone->lsdb,lsa1); //old lsa will be delete here
            ospf_lsa_install(ospf,NULL,lsa_dup);

            zlog_debug("after lsa1 install 1,lsa1->data->type=%d",lsa1->data->type);
            break;
          }
          zlog_debug("after lsa1 install 2");
        }
        zlog_debug("after lsa1 install 3");
      }
      zlog_debug("install a lsa success");
    }
  }
  */
  for(rn1=route_top(vty_test_db->type[OSPF_ROUTER_LSA].db);rn1;rn1=route_next(rn1))
  {
    lsa1=(struct ospf_lsa *)rn1->info;
    if(lsa1!=NULL)
    {

        lsa_dup=ospf_lsa_dup(lsa1);
        lsa_dup->area=area;
        lsa_dup->lsdb=ospf->backbone->lsdb;
        ospf_lsa_install(ospf,NULL,lsa_dup);

        zlog_debug("after lsa1 install 1,lsa1->data->type=%d",lsa1->data->type);
    }
  }
  return CMD_SUCCESS;
}

DEFUN(see_lsdb,
      see_lsdb_cmd,
      "see_lsdb",
      "see lsdb in debug\n")
{
  struct ospf *ospf=ospf_lookup ();

  struct ospf_lsa *lsa;

  struct route_node *rn;
  struct route_table *db;
  struct ospf_area *area;
  zlog_debug("in func see lsdb");
  area=ospf->backbone;
  db=ospf->backbone->lsdb->type[OSPF_ROUTER_LSA].db;
  if(area==NULL || db==NULL)
  {
    return CMD_WARNING;
  }

  for(rn=route_top(db);rn;rn=route_next(rn))
  {
    zlog_debug("rn->id=%x,prefixlen=%d",rn->p.u.prefix4.s_addr,rn->p.prefixlen);
    lsa=(struct ospf_lsa *)rn->info;
    if(lsa!=NULL)
    {
      zlog_debug("lsa->phase=%d",lsa->phase_count);
      zlog_debug("lsa->link=%d",lsa->links_count);
    }
  }

  return CMD_SUCCESS;
}

DEFUN(print_ospf_info,
      print_ospf_info_cmd,
      "print_ospf_info",
      "print ospf info\n")
{
  struct ospf *ospf=ospf_lookup ();
  struct ospf_lsa *lsa;
  lsa=ospf->backbone->router_lsa_self;
  zlog_debug("in func print_ospf_info");
  zlog_debug("router_lsa_self,lsa->id=%x,lsa->adv-router=%x",lsa->data->id.s_addr,lsa->data->adv_router.s_addr);
  if(lsa->phase_count!=0)
  {
    zlog_debug("lsa->phase_count=%d",lsa->phase_count);
  }

  struct listnode *node;
  struct ospf_area *area;
  for (ALL_LIST_ELEMENTS_RO (ospf->areas, node, area))
  {
    zlog_debug("area->id=%x",area->area_id.s_addr);
  }
  return CMD_SUCCESS;
}


static void print_nbr_rxmt_sub(){
  struct ospf *ospf=ospf_lookup ();
  struct listnode *node,*nnode;
  struct ospf_interface *oi;
  struct route_node *rn,*rn1;
  struct ospf_neighbor *nbr;
  struct ospf_lsdb *lsdb;
  struct route_table *db;
  int i;

  for(ALL_LIST_ELEMENTS(ospf->oiflist, node, nnode, oi))
  {
    for(rn=route_top(oi->nbrs); rn;  rn=route_next(rn))
    {

      zlog_debug("nbr->id=%x,prefixlen=%d",rn->p.u.prefix4.s_addr,rn->p.prefixlen);
      nbr=(struct ospf_neighbor *)rn->info;
      
      if((nbr!=NULL))
      {
        //can not use rn inside
         
        lsdb=&nbr->ls_rxmt;
        

        zlog_debug("in change_lsdb_sub,exam ls_rxmt");
        for(i=0;i<8;++i)
        {
          db=lsdb->type[i].db;
          zlog_debug("in change_lsdb_sub:lsdb type=%d",i);
          if(db==NULL)
          {
            zlog_debug("db==NULL");
            continue;
          }

          for(rn1=route_top(db);rn1;rn1=route_next(rn1))
          {
            zlog_debug("rn->prefix=%d,prefixlen=%d",rn1->p.u.prefix4.s_addr,(int)rn1->p.prefixlen);
            if(rn1->info)
            {
              zlog_debug("this rn have info");
            }
          }
        }
        lsdb=&nbr->ls_req;
        zlog_debug("in change_lsdb_sub,exam ls_req");
        for(i=0;i<8;++i)
        {
          db=lsdb->type[i].db;
          zlog_debug("in change_lsdb_sub:lsdb type=%d",i);

          if(db==NULL)
          {
            zlog_debug("db==NULL");
            continue;
          }
          for(rn1=route_top(db);rn1;rn1=route_next(rn1))
          {
            zlog_debug("rn->prefix=%d,prefixlen=%d",rn1->p.u.prefix4.s_addr,(int)rn1->p.prefixlen);
            if(rn1->info)
            {
              zlog_debug("this rn have info");
            }
          }
        }
        lsdb=&nbr->db_sum;
        zlog_debug("in change_lsdb_sub,exam dbsum");
        for(i=0;i<8;++i)
        {
          db=lsdb->type[i].db;
          zlog_debug("in change_lsdb_sub:lsdb type=%d",i);
          if(db==NULL)
          {
            zlog_debug("db==NULL");
            continue;
          }
          for(rn1=route_top(db);rn1;rn1=route_next(rn1))
          {
            zlog_debug("rn->prefix=%d,prefixlen=%d",rn1->p.u.prefix4.s_addr,(int)rn1->p.prefixlen);
            if(rn1->info)
            {
              zlog_debug("this rn have info");
            }
          }
        }
        
        zlog_debug("finish a nbr!=NULL");

      }
      
      zlog_debug("finish a nbr");
      
    }
    zlog_debug("finish an oi");
  }
}
DEFUN( print_nbr_rxmt,
       print_nbr_rxmt_cmd,
       "print_nbr_rxmt",
       "print_nbr_rxmt\n")
{
  print_nbr_rxmt_sub();
  return CMD_SUCCESS;
}

void spf_change_phase_sub(int phase)
{
  //change tos according to phase_matrix;
  struct ospf *ospf=ospf_lookup();
  
  struct  route_table *rt=ospf->backbone->lsdb->type[OSPF_ROUTER_LSA].db;
  
  struct route_node *rn;
  struct ospf_lsa *lsa;
  struct router_lsa *rl;

  zlog_debug("in func spf_change_phase_sub");

  for(rn=route_top(rt);rn;rn=route_next(rn))
  {
    lsa=rn->info;
    if(lsa==NULL)
    {
      continue;
    }
    else
    {
      rl=(struct router_lsa *)lsa->data;
      zlog_debug("phase_count=%d,links_count=%d",lsa->phase_count,lsa->links_count);
      //zlog_debug("before change:length=%d",rl->header.length);
      //zlog_debug("before change:ntohs length=%d",ntohs(rl->header.length));
      //if lsa do't have phase, nothing will happen
      if(lsa->phase_count!=0 && lsa->phase_matrix!=NULL)
      {
        for(int i=0;i<lsa->links_count;++i)
        {
          if(lsa->phase_matrix[i][phase]==1)
            rl->link[i].tos=(u_char)0x01;
          else
            rl->link[i].tos=(u_char)0x00;
          //zlog_debug("rl->link[%d].tos=%d",i,rl->link[i].tos);
          //zlog_debug("rl->link[%d].type=%d",i,rl->link[i].type);
        }
      }
      //zlog_debug("after change:length=%d",rl->header.length);
      //zlog_debug("after change:ntohs length=%d",ntohs(rl->header.length));
    }
  }
  ospf_spf_calculate_schedule(ospf);
}


DEFUN( spf_change_phase,
       spf_change_phase_cmd,
       "spfchangephase <0-100>",
       "spfchange to specific phase\n")
{

  int phase_1=atoi(argv[0]);

  spf_change_phase_sub(phase_1);

  return CMD_SUCCESS;
}

static int
ospf_predicted_link_down_timer (struct thread *thread)
{
  struct ospf_neighbor *nbr;

  nbr = THREAD_ARG (thread);
  nbr->t_predown = NULL;
  OSPF_NSM_EVENT_EXECUTE(nbr,NSM_PredictedLinkDown);
  zlog_debug("predown timer has executed");
  return 0;
}

void predicted_linkdown_sub(struct in_addr nbr_addr)
{
  struct ospf_neighbor *nbr;
  struct ospf *ospf;
  struct listnode *node,*nnode;
  struct ospf_interface *oi;
  struct route_node *rn;

  zlog_debug("in func predicted_linkdown_sub");
  ospf=ospf_lookup ();
  for(ALL_LIST_ELEMENTS(ospf->oiflist, node, nnode, oi))
  {
    for(rn=route_top(oi->nbrs); rn;  rn=route_next(rn))
    {
      if((nbr=(struct ospf_neighbor *)rn->info))
      {
        zlog_debug("in predictedlinkdown %x",nbr->router_id.s_addr);

        if(nbr->router_id.s_addr == nbr_addr.s_addr)
        {
          zlog_debug("find nbr in predictedlinkdown %x, and predown timer is on",nbr->router_id.s_addr);
          OSPF_NSM_TIMER_ON(nbr->t_predown,ospf_predicted_link_down_timer,nbr->v_test);
          break;
        }
      }
    }
  }

}



DEFUN( predicted_linkdown,
       predicted_linkdown_cmd,
       "predictedlinkdown A.B.C.D",
       "linkdown the neighbor\n")
{
  struct in_addr nbr_addr;
  VTY_GET_IPV4_ADDRESS ("neighbor address", nbr_addr, argv[0]);
  predicted_linkdown_sub(nbr_addr);
  return CMD_SUCCESS;
}

void predicted_linkup_sub(struct in_addr nbr_addr)
{
  struct ospf_neighbor *nbr;
  struct ospf *ospf;
  struct listnode *node,*nnode;
  struct ospf_interface *oi;
  struct route_node *rn;
  ospf=ospf_lookup ();
  for(ALL_LIST_ELEMENTS(ospf->oiflist, node, nnode, oi))
  {
    for(rn=route_top(oi->nbrs); rn;  rn=route_next(rn))
    {
      zlog_debug("nbr->id=%x,prefixlen=%d",rn->p.u.prefix4.s_addr,rn->p.prefixlen);
      if((nbr=(struct ospf_neighbor *)rn->info))
      {
        zlog_debug("in predictedlinkup %x",nbr->router_id.s_addr);
        if(nbr->router_id.s_addr == nbr_addr.s_addr)
        {
          zlog_debug("find nbr in predictedlinkup %x",nbr->router_id.s_addr);
          OSPF_NSM_EVENT_EXECUTE (nbr, NSM_PredictedLinkUp);
        }
      }
    }
  }

}

DEFUN( predicted_linkup,
       predicted_linkup_cmd,
       "predictedlinkup A.B.C.D",
       "linkup the neighbor\n")
{


  struct in_addr nbr_addr;
  VTY_GET_IPV4_ADDRESS ("neighbor address", nbr_addr, argv[0]);
  predicted_linkup_sub(nbr_addr);
  //OSPF_NSM_EVENT_EXECUTE (nbr, NSM_PredictedLinkDown);
  return CMD_SUCCESS;
}

DEFUN(spf_test,
      spf_test_cmd,
      "spftest",
      "test spf and cal time\n")
{
  struct ospf *ospf=ospf_lookup();
  zlog_debug("begin a spf time test");
  ospf_spf_calculate_schedule(ospf);
  return CMD_SUCCESS;
}



struct neighbor_info_list *neighbor_info_list_cur;
struct ase_info_list *ase_info_list_cur;


struct neighbor_info *neighbor_info_new(void)
{
  struct neighbor_info *nbr_info=calloc(1,sizeof(struct neighbor_info));
  nbr_info->phase_info=NULL;
  return(nbr_info);
}


void neighbor_info_free(void *neighbor_info)
{
  if(neighbor_info!=NULL)
  {
    if(((struct neighbor_info *)neighbor_info)->phase_info)
    {
      free(((struct neighbor_info *)neighbor_info)->phase_info);
    }
    free((struct neighbor_info *)neighbor_info);
  }
}

struct neighbor_info_list *neighbor_info_list_new(void)
{
  struct neighbor_info_list *neighborinfolist=(struct neighbor_info_list *)calloc(1,sizeof(struct neighbor_info_list));
  
  neighborinfolist->n_list=list_new();
  neighborinfolist->n_list->del=neighbor_info_free;
  return neighborinfolist;
}


void neighbor_info_list_free(struct neighbor_info_list *neighborinfolist)
{
  if(neighborinfolist->n_list!=NULL)
  {
    list_delete(neighborinfolist->n_list);
  }
  free(neighborinfolist);
}

static void print_nbr_info_list()
{
  zlog_debug("begin print nbr info list");
  zlog_debug("neighbor:%d,phase:%d",neighbor_info_list_cur->neighborcount,neighbor_info_list_cur->phasecount);
  struct listnode *node, *nnode;
  struct neighbor_info *nbr_info;

  for( ALL_LIST_ELEMENTS(neighbor_info_list_cur->n_list,node,nnode,nbr_info) )
  {
    zlog_debug("router-id:%x,if_addr:%x",nbr_info->router_id.s_addr,nbr_info->if_addr.s_addr);
    for(int i=0;i<neighbor_info_list_cur->phasecount;++i)
    {
      zlog_debug("phase%d:%d",i,nbr_info->phase_info[i]);
    }
  }
}


void read_neighbor_info(const char *filename)
{
  DATA_INFO_STR nbr_str;
  fileToMatrix_str(filename, & nbr_str);
  int i,j,nbr_count,phase_count;
  struct neighbor_info *nbr_info;


  nbr_count=atoi(nbr_str.matrix[0][0]);
  phase_count=atoi(nbr_str.matrix[0][1]);

  neighbor_info_list_cur->neighborcount = nbr_count;
  neighbor_info_list_cur->phasecount = phase_count;

  for(i=1;i<nbr_count+1;++i)
  {
    zlog_debug("in read neighbor info,%s",nbr_str.matrix[i][0]);

    nbr_info=neighbor_info_new();
    inet_aton(nbr_str.matrix[i][0], &nbr_info->router_id);
    

    nbr_info->phase_info=calloc(phase_count,sizeof(int));
    for(j=1; j<nbr_str.line_total[i]; ++j)
    {
      zlog_debug("%s",nbr_str.matrix[i][j]);

      nbr_info->phase_info[j-1]=atoi(nbr_str.matrix[i][j]);
    }
    listnode_add(neighbor_info_list_cur->n_list,nbr_info);

  }

  print_nbr_info_list();

}


DEFUN(readneighbor,
      readneighbor_cmd,
      "readneighbor FILENAME",
      "read neighbor info from txt\n")
{
  read_neighbor_info(argv[0]);
  return CMD_SUCCESS;
}

DEFUN(print_neighbor,
      print_neighbor_cmd,
      "print_neighbor",
      "print neighbor\n")
{
  print_nbr_info_list();
  return CMD_SUCCESS;
}



static int
ospf_test_timer (struct thread *thread)
{
  struct ospf_neighbor *nbr;

  nbr = THREAD_ARG (thread);
  nbr->t_test = NULL;

  struct timeval help_time;
  quagga_gettime (QUAGGA_CLK_MONOTONIC,&help_time);

  zlog_debug ("TEST[%s:%s]: test_timer end at %ld.%ld", IF_NAME (nbr->oi), inet_ntoa (nbr->router_id),help_time.tv_sec,help_time.tv_usec);


  return 0;
}


DEFUN(test_timer,
      test_timer_cmd,
      "test_timer A.B.C.D <1-100>",
      "test timer func\n")
{
  struct in_addr nbr_addr;
  VTY_GET_IPV4_ADDRESS ("neighbor address", nbr_addr, argv[0]);
  u_int32_t v_test;
  v_test=(u_int32_t)atoi(argv[1]);

  struct ospf_neighbor *nbr;
  struct ospf *ospf;
  struct listnode *node,*nnode;
  struct ospf_interface *oi;
  struct route_node *rn;
  struct timeval help_time;

  ospf=ospf_lookup ();
  for(ALL_LIST_ELEMENTS(ospf->oiflist, node, nnode, oi))
  {
    for(rn=route_top(oi->nbrs); rn;  rn=route_next(rn))
    {
      if((nbr=(struct ospf_neighbor *)rn->info))
      {

        if(nbr->router_id.s_addr == nbr_addr.s_addr)
        {
          quagga_gettime (QUAGGA_CLK_MONOTONIC,&help_time);
          zlog_debug("in timer_test %x,test_timer begin at %ld.%ld",nbr->router_id.s_addr,help_time.tv_sec,help_time.tv_usec);
          
          OSPF_NSM_TIMER_ON(nbr->t_test,ospf_test_timer,v_test);
        }
      }
    }
  }

  return CMD_SUCCESS;
}


int
ospf_predicted_link_up_timer (struct thread *thread)
{
  struct ospf_neighbor *nbr;

  nbr = THREAD_ARG (thread);
  nbr->t_test = NULL;

  OSPF_NSM_EVENT_EXECUTE(nbr,NSM_PredictedLinkUp);


  return 0;
}

void begin_testing_sub(struct in_addr nbr_addr,u_int32_t v_test)
{
  struct ospf_neighbor *nbr;
  struct ospf *ospf;
  struct listnode *node,*nnode;
  struct ospf_interface *oi;
  struct route_node *rn;
  struct timeval help_time;

  ospf=ospf_lookup ();
  for(ALL_LIST_ELEMENTS(ospf->oiflist, node, nnode, oi))
  {
    for(rn=route_top(oi->nbrs); rn;  rn=route_next(rn))
    {
      if((nbr=(struct ospf_neighbor *)rn->info))
      {

        if(nbr->router_id.s_addr == nbr_addr.s_addr)
        {
          quagga_gettime (QUAGGA_CLK_MONOTONIC,&help_time);
          zlog_debug("in begin_testing %x,ospf_predicted_link_up_timer begin at %ld.%ld",nbr->router_id.s_addr,help_time.tv_sec,help_time.tv_usec);
          if(v_test!=0)
          {
            nbr->v_test=v_test;
          }
          OSPF_NSM_EVENT_EXECUTE(nbr,NSM_BeginTesting);
          OSPF_NSM_TIMER_ON(nbr->t_test,ospf_predicted_link_up_timer,nbr->v_test);
        }
      }
    }
  }
}


DEFUN(begin_testing,
      begin_testing_cmd,
      "begin_testing A.B.C.D <1-100>",
      "begin_testing A.B.C.D <1-100>\n")
{
  struct in_addr nbr_addr;
  VTY_GET_IPV4_ADDRESS ("neighbor address", nbr_addr, argv[0]);
  u_int32_t v_test;
  v_test=(u_int32_t)atoi(argv[1]);

  begin_testing_sub(nbr_addr,v_test);
  return CMD_SUCCESS;
}

DEFUN(set_phase_all,
     set_phase_all_cmd,
     "set_phase_all <1-1000>",
     "set phase_all <1-1000>\n")
{
  phase_all=atoi(argv[0]);
  zlog_debug("in func set_phase_all, phase_all=%d",phase_all);
  return CMD_SUCCESS;
} 
//return 0 if lsa is recover, otherwise return 1
static int is_lsa_recover(struct ospf_lsa *lsa,struct ospf_lsa *lsa_phase,int phase)
{
  assert(lsa->phase_count==0);
  assert(lsa_phase->phase_count!=0);
  struct router_lsa *rl=(struct router_lsa *)lsa->data;
  //struct router_lsa *rl_phase=lsa_phase->data;
  int link_to_check=0;
  //get links_to_check number from phase_matrix 
  for(int i=0;i<lsa_phase->links_count;++i)
  {
    if(lsa_phase->phase_matrix[i][phase]==0)
    {
      zlog_debug("in func is_lsa_recover, this is a link to check");
      link_to_check++;
    }

  }
  //check links in lsa
  //roughly consider links same equal lsa same,don't consider cases that links different but count same
  int link_in_lsa_receive=(int)ntohs(rl->links);
  zlog_debug("in func is_lsa_recover,links1=%d,links2=%d",link_to_check,link_in_lsa_receive);
  if(link_in_lsa_receive==link_to_check)
  {
    return 0;
  }
  else
  {
    return 1;
  }
}

DEFUN(test_is_lsa_recover,
      test_is_lsa_recover_cmd,
      "test_is_lsa_recover <1-1000>",
      "test is_lsa_recover <1-1000(phase)>\n")

{
  struct ospf *ospf=ospf_lookup ();
  //struct ospf_lsdb *tmp;
  struct ospf_lsa *lsa,*lsa1;
  //struct router_lsa *rl;
  struct route_node *rn,*rn1;
  struct route_table *db;
  struct ospf_area *area;
  zlog_debug("in func test_is_lsa_recover");
  area=ospf->backbone;
  db=ospf->backbone->lsdb->type[OSPF_ROUTER_LSA].db;

  int test_result;
  int test_phase=atoi(argv[0]);

  if(area==NULL || db==NULL)
  {
    return CMD_WARNING;
  }

  for(rn=route_top(db);rn;rn=route_next(rn))
  {
    lsa=(struct ospf_lsa *)rn->info;
    if(lsa!=NULL)
    {
      zlog_debug("lsa->id=%x",lsa->data->id.s_addr);
      if(lsa->phase_count!=0)
      {
        zlog_debug("this lsa has phase,continue");
        continue;
      }
      for(rn1=route_top(vty_test_db->type[OSPF_ROUTER_LSA].db);rn1;rn1=route_next(rn1))
      {
        lsa1=(struct ospf_lsa *)rn1->info;
        if(lsa1!=NULL)
        {

          if(lsa1->data->id.s_addr==lsa->data->id.s_addr)
          {
            test_result=is_lsa_recover(lsa,lsa1,test_phase);
            zlog_debug("test_result=%d",test_result);
          }
        }
      }
    }
  }  
  return CMD_SUCCESS;
}




DEFUN(print_ase,
      print_ase_cmd,
      "print_ase",
      "print ase\n")
{
  struct ospf *ospf=ospf_lookup ();
  //struct listnode *node;
  //struct ospf_interface *oi;
  struct route_node *rn;
  //struct ospf_neighbor *nbr;
  //struct ospf_lsdb *lsdb;
  struct route_table *rt;


  rt=ospf->lsdb->type[OSPF_AS_EXTERNAL_LSA].db;

  zlog_debug("in print_ase, print ospf->lsdb");
  for(rn=route_top(rt);rn;rn=route_next(rn))
  {
    zlog_debug("rn->prefix=%x,prefixlength=%d",rn->p.u.prefix4.s_addr,rn->p.prefixlen);
    zlog_debug("rn->lp.id=%x,lp.adv_router=%x",rn->p.u.lp.id.s_addr,rn->p.u.lp.adv_router.s_addr);
    if((rn->info))
    {
      zlog_debug("this rn has info");
    }
  }
  zlog_debug("in print_ase, print external_lsas");
  rt=ospf->external_lsas;
  for(rn=route_top(rt);rn;rn=route_next(rn))
  {
    zlog_debug("rn->prefix=%x,prefixlength=%d",rn->p.u.prefix4.s_addr,rn->p.prefixlen);
    zlog_debug("rn->lp.id=%x,lp.adv_router=%x",rn->p.u.lp.id.s_addr,rn->p.u.lp.adv_router.s_addr);
    if((rn->info))
    {
      zlog_debug("this rn has info");
    }
  }
  return CMD_SUCCESS;
}
DEFUN(print_backbone,
      print_backbone_cmd,
      "print_backbone",
      "print backbone\n")
{
  struct ospf *ospf=ospf_lookup ();
  //struct listnode *node,*nnode;
  //struct ospf_interface *oi;
  struct route_node *rn;
  //struct ospf_neighbor *nbr;
  //struct ospf_lsdb *lsdb;
  struct route_table *rt;


  rt=ospf->backbone->lsdb->type[OSPF_ROUTER_LSA].db;

  zlog_debug("in print_backbone, print ospf->backbone->lsdb->type[OSPF_ROUTER_LSA].db");
  for(rn=route_top(rt);rn;rn=route_next(rn))
  {
    zlog_debug("rn->prefix=%x,prefixlength=%d",rn->p.u.prefix4.s_addr,rn->p.prefixlen);
    zlog_debug("rn->lp.id=%x,lp.adv_router=%x",rn->p.u.lp.id.s_addr,rn->p.u.lp.adv_router.s_addr);
    if((rn->info))
    {
      zlog_debug("this rn has info");
    }
  }
  /*
  zlog_debug("in print_ase, print external_lsas");
  rt=ospf->external_lsas;
  for(rn=route_top(rt);rn;rn=route_next(rn))
  {
    zlog_debug("rn->prefix=%x,prefixlength=%d",rn->p.u.prefix4.s_addr,rn->p.prefixlen);
    zlog_debug("rn->lp.id=%x,lp.adv_router=%x",rn->p.u.lp.id.s_addr,rn->p.u.lp.adv_router.s_addr);
    if((rn->info))
    {
      zlog_debug("this rn has info");
    }
  }*/
  return CMD_SUCCESS;
}
DEFUN(print_phase,
      print_phase_cmd,
      "print_phase",
      "print phase info\n")
{
  zlog_debug("in func print phase,phase_all=%d,global_phase=%d",phase_all,global_phase);
  return CMD_SUCCESS;
}

DEFUN(ase_output,
      ase_output_cmd,
      "ase_output FILENAME",
      "output as-external-lsa to file\n")
{
  zlog_debug("in func ase_output");
  struct ospf *ospf=ospf_lookup ();
  if(ospf==NULL){
    zlog_debug("find ospf fail");
    return CMD_WARNING;
  }

  struct route_table *rt;
  struct route_node *rn;
  struct ospf_lsa *lsa;
  struct as_external_lsa *ase;
  struct lsa_header *lsh;
  FILE *file;

  rt=ospf->lsdb->type[OSPF_AS_EXTERNAL_LSA].db;

  file=fopen(argv[0],"w+");
  if(file==NULL){
    vty_out(vty,"open fail%s",VTY_NEWLINE);
    return CMD_WARNING;
  }

  for(rn=route_top(rt);rn; rn=route_next(rn))
  {
    if((lsa=(struct ospf_lsa*)rn->info)!=NULL)
    {
      ase=(struct as_external_lsa *)lsa->data;
      lsh=&ase->header;
      fprintf(file,"!,%d,%d,%d,%s,",ntohs(lsh->ls_age),lsh->options,lsh->type,inet_ntoa(lsh->id)); 
      fprintf(file,"%s,%d,%d,%d,\n",inet_ntoa(lsh->adv_router),ntohl(lsh->ls_seqnum),ntohs(lsh->checksum),ntohs(lsh->length));
      fprintf(file,"@,%s,%u,%u,%u,%u,",inet_ntoa(ase->mask),ase->e[0].tos, ase->e[0].metric[0], ase->e[0].metric[1], ase->e[0].metric[2]);
      fprintf(file,"%s,%d,\n", inet_ntoa(ase->e[0].fwd_addr),ntohl(ase->e[0].route_tag));
      fprintf(file,"#,%d,",lsa->phase_count);
      if(lsa->phase_count!=0 && lsa->phase_matrix!=NULL)
      {
        for(int i=0;i<lsa->phase_count;++i)
        {
          fprintf(file,"%d,",lsa->phase_matrix[0][i]);
        }
      }
      fprintf(file,"\n");
    }
  }

  fclose(file);
  return CMD_SUCCESS;
}

DEFUN(ase_input,
      ase_input_cmd,
      "ase_input FILENALE",
      "ase_input FILENAME\n")
{

  DATA_INFO_STR data_info_str;

  fileToMatrix_str(argv[0],&data_info_str);
  if(data_info_str.row_total==0)
  {
    return CMD_WARNING;
  }
  zlog_debug("in func ase_input");
  int i,j,lsa_length;
  struct ospf_lsa *lsa;
  struct stream *s=NULL;
  struct lsa_header *lsah;
  struct in_addr temp_addr;
  struct route_node *rn;
  struct ospf *ospf=ospf_lookup ();
  lsa_length=OSPF_LSA_HEADER_SIZE+16;

  zlog_debug("begin reading ase lsdb,row_total=%d",data_info_str.row_total);
  
  for(i=0;i<data_info_str.row_total;++i)
  {
    zlog_debug("data_info_str.matrix[%d][0]=%s",i,data_info_str.matrix[i][0]);
    if(data_info_str.matrix[i][0][0]=='!')
    {
      zlog_debug("in line begin with !");
      s=stream_new (OSPF_MAX_LSA_SIZE);
      lsa=ospf_lsa_new();
      zlog_debug("0.1");
      lsah=(struct lsa_header *) STREAM_DATA (s);
      zlog_debug("0.2");
      lsah->ls_age=htons (OSPF_LSA_INITIAL_AGE);
      zlog_debug("0.3");
      lsah->options=(u_char) atoi (data_info_str.matrix[i][2]);
      zlog_debug("0.4");
      lsah->type=(u_char)atoi (data_info_str.matrix[i][3]);
      zlog_debug("1");
      inet_aton(data_info_str.matrix[i][4],&temp_addr);
      lsah->id.s_addr=temp_addr.s_addr;
      zlog_debug("2");
      inet_aton(data_info_str.matrix[i][5],&temp_addr);
      lsah->adv_router.s_addr=temp_addr.s_addr;
      zlog_debug("3");
      lsah->ls_seqnum=htonl(atoi(data_info_str.matrix[i][6])+1);
      zlog_debug("4");
      //lsah->checksum will calc in the end, because seqnum will change
      
      lsah->length=htons(atoi(data_info_str.matrix[i][8]));
      zlog_debug("5");
      stream_forward_endp (s, OSPF_LSA_HEADER_SIZE); 
      

      zlog_debug("lsa header write successful");
    }

    else if(data_info_str.matrix[i][0][0]=='@')
    {
      zlog_debug("in line begin with @");
      inet_aton(data_info_str.matrix[i][1],&temp_addr);
      stream_putl(s,htonl(temp_addr.s_addr));
      stream_putc (s,atoi(data_info_str.matrix[i][2]));
      stream_putc (s,atoi(data_info_str.matrix[i][3]));
      stream_putc (s,atoi(data_info_str.matrix[i][4]));
      stream_putc (s,atoi(data_info_str.matrix[i][5]));
      inet_aton(data_info_str.matrix[i][6],&temp_addr);
      stream_putl(s,htonl(temp_addr.s_addr));
      stream_putl(s,htonl ( atoi( data_info_str.matrix[i][7]) ) );
      
      lsa->data=ospf_lsa_data_new (lsa_length);
      lsah=(struct lsa_header *) STREAM_DATA (s);
      memcpy(lsa->data,STREAM_DATA (s),lsa_length);

      ospf_lsa_is_self_originated(ospf,lsa);
      lsah->checksum=ospf_lsa_checksum(lsah);

      lsa->lock=1;
      lsa->lsdb=vty_test_db;

    }
    else if(data_info_str.matrix[i][0][0]=='#')
    {
      zlog_debug("in line begin with #");

      lsa->links_count=1;
      lsa->phase_count=atoi(data_info_str.matrix[i][1]);

      zlog_debug("lsa->phase_count=%d",lsa->phase_count);

      lsa->phase_matrix=(int **)calloc(1,sizeof(int *));
      lsa->phase_matrix[0]=(int *)calloc(lsa->phase_count,sizeof(int ));
      for(j=2;j<lsa->phase_count+2;++j)
      {
        lsa->phase_matrix[0][j-2]=atoi(data_info_str.matrix[i][j]);
        zlog_debug("lsa->phase_mat[0][%d]=%d",j-2,lsa->phase_matrix[0][j-2]);
      }

      ospf_lsdb_add(vty_test_db,lsa);
      stream_free(s);
      s=NULL;
    }


  }
  ase_info_list_cur->adv_router_count=0;
  ase_info_list_cur->ase_list=list_new();
  struct listnode *node, *nnode;
  struct as_external_lsa *ase;
  struct ase_info *ase_info;
  int find_flag=0;

  struct prefix *p;
  p=prefix_new();

  for(rn=route_top(vty_test_db->type[OSPF_AS_EXTERNAL_LSA].db);rn;rn=route_next(rn))
  {
    find_flag=0;
    if(rn->info!=NULL)
    {
      
      lsa=(struct ospf_lsa *)rn->info;
      ase=(struct as_external_lsa *)lsa->data; 
      
      p->u.prefix4.s_addr=ase->header.id.s_addr;
      p->prefixlen=ip_masklen(ase->mask);
      if(prefix_match(se_prefix,p))
      {
        zlog_debug("in ase_input,add ase_list,ase->id=%x/%d,pass",ase->header.id.s_addr,p->prefixlen);
        continue;
      }

      for(ALL_LIST_ELEMENTS(ase_info_list_cur->ase_list,node,nnode,ase_info))
      {
        if(ase_info->adv_router.s_addr==ase->header.adv_router.s_addr)
        {
          find_flag=1;
          listnode_add(ase_info->ase_lsa,lsa);
          ase_info->lsa_count++;  
        }
      }

      if(find_flag==0)
      {
        
        ase_info=calloc(1,sizeof(struct ase_info));
        
        ase_info->adv_router.s_addr=ase->header.adv_router.s_addr;
        ase_info->lsa_count=1;
        ase_info->ase_lsa=list_new();
        listnode_add(ase_info->ase_lsa,lsa);

        listnode_add(ase_info_list_cur->ase_list,ase_info);
        ase_info_list_cur->adv_router_count++;
      }

    }
  }

  return CMD_SUCCESS;
}

DEFUN(ase_changelsdb,
      ase_changelsdb_cmd,
      "ase_change_lsdb",
      "ase_change_lsdb\n")
{
  struct ospf *ospf=ospf_lookup ();
  struct ospf_lsdb *tmp;

  tmp=ospf->lsdb;
  ospf->lsdb=vty_test_db;
  vty_test_db=tmp;
  return CMD_SUCCESS;
}
DEFUN(ase_loadlsdb,
      ase_loadlsdb_cmd,
      "ase_loadlsdb",
      "ase_loadlsdb")
{
  struct ospf *ospf=ospf_lookup();
  struct ospf_lsa *lsa,*lsa_dup;
  struct route_node *rn;
  struct route_table *db;
  zlog_debug("in func ase_loadlsdb");
  db=vty_test_db->type[OSPF_AS_EXTERNAL_LSA].db;
  if(db==NULL)
  {
    return CMD_WARNING;
  }
  for(rn=route_top(db);rn;rn=route_next(rn))
  {
    if((lsa=(struct ospf_lsa*)rn->info)!=NULL)
    {
      lsa_dup=ospf_lsa_dup(lsa);
      lsa_dup->lsdb=ospf->lsdb;
      lsa_dup->area=NULL;
      ospf_lsa_install(ospf,NULL,lsa_dup);
    }
  }

  return CMD_SUCCESS;
}
DEFUN(print_ase_info,
      print_ase_info_cmd,
      "print_ase_info",
      "print_ase_info\n")
{

  struct listnode *node, *nnode,*node1,*nnode1;
  struct ospf_lsa *lsa;

  struct ase_info *ase_info;

  zlog_debug("in func print_ase_info,ase->adv_router_cnt=%d",ase_info_list_cur->adv_router_count);

  for(ALL_LIST_ELEMENTS(ase_info_list_cur->ase_list,node,nnode,ase_info))
  {
    zlog_debug("ase_info: adv_router=%x,lsa_count=%d",ase_info->adv_router.s_addr,ase_info->lsa_count);
    for(ALL_LIST_ELEMENTS(ase_info->ase_lsa,node1,nnode1,lsa))
    {
      zlog_debug("lsa->id=%x,lsa->phase=%d",lsa->data->id.s_addr,lsa->phase_count);
    }
  }

  return CMD_SUCCESS;
}
//return 1 if lsa dont recover or dont change,else return 0,and should load lsa
static int is_ase_recover(struct in_addr adv_addr,int phase)
{
  struct ospf *ospf=ospf_lookup();
  struct route_table *rt;
  struct route_node *rn;
  struct ospf_lsa *lsa;
  struct as_external_lsa *ase;
  int ase_count=0;
  int phase_ase_count=0;
  struct listnode *node,*nnode,*node1,*nnode1;
  struct ase_info *ase_info;
  rt=ospf->lsdb->type[OSPF_AS_EXTERNAL_LSA].db;

  int change_flag=0;
  for(rn=route_top(rt);rn;rn=route_next(rn))
  {
    if(rn->info!=NULL)
    {
      lsa=(struct ospf_lsa *)rn->info;
      ase=(struct as_external_lsa *)lsa->data;
      if(ase->header.adv_router.s_addr==adv_addr.s_addr && lsa->phase_count==0)
      {
        change_flag=1;
        break;
      }      
    }
  }



  for(rn=route_top(rt);rn;rn=route_next(rn))
  {
    if(rn->info!=NULL)
    {
      lsa=(struct ospf_lsa *)rn->info;
      ase=(struct as_external_lsa *)lsa->data;
      if(ase->header.ls_age < OSPF_LSA_MAXAGE && ase->header.adv_router.s_addr==adv_addr.s_addr)
      {

        ase_count++;
      }
    }
  }

  for(ALL_LIST_ELEMENTS(ase_info_list_cur->ase_list,node,nnode,ase_info))
  {
    if(ase_info->adv_router.s_addr==adv_addr.s_addr)
    {
      for(ALL_LIST_ELEMENTS(ase_info->ase_lsa,node1,nnode1,lsa))
      {

        if(lsa->phase_matrix[0][phase]==0)
        {
          phase_ase_count++;
        }
      }
      break;
    }
  }
  zlog_debug("phase=%d,phase_ase_count=%d,ase_count=%d",phase,phase_ase_count,ase_count);
  if(phase_ase_count<=ase_count && change_flag==1)
  {
    zlog_debug("in func is_ase_recover adv_addr=%x has recover",adv_addr.s_addr);

    return 0;
  }
  else
  {
    zlog_debug("in func is_ase_recover adv_addr=%x hasn't recover or don't change",adv_addr.s_addr);
    return 1;
  }


}

static void manage_ase(int phase)
{
  struct listnode *node,*nnode,*node1,*nnode1;
  struct ase_info *ase_info;
  struct ospf_lsa *lsa,*lsa_dup;
  int test_result;
  struct ospf *ospf=ospf_lookup();
  for(ALL_LIST_ELEMENTS(ase_info_list_cur->ase_list,node,nnode,ase_info))
  {

    test_result=is_ase_recover(ase_info->adv_router,phase);
    if(test_result==1)
    {
      //do not recover or dont change, do noting
      continue;
    }
    else
    {
      //has recover, dup ase_phase_lsa into lsdb
      for(ALL_LIST_ELEMENTS(ase_info->ase_lsa,node1,nnode1,lsa))
      {
        lsa_dup=ospf_lsa_dup(lsa);
        lsa_dup->lsdb=ospf->lsdb;
        lsa_dup->area=NULL;
        ospf_lsa_install(ospf,NULL,lsa_dup);

      }
    }
  }
}

DEFUN(test_manage_ase,
      test_manage_ase_cmd,
      "test_manage_ase <0-100>",
      "test manage_ase func\n")
{
  int phase=atoi(argv[0]);
  zlog_debug("in func test_manage_ase, phase=%d",phase);
  manage_ase(phase);
  return CMD_SUCCESS;
}

int last_phase;


//lsa should be manage before spf calc
static int
ospf_spf_help_timer (struct thread *thread)
{
  struct ospf *ospf;

  ospf = THREAD_ARG (thread);
  ospf->t_spf_help=NULL;

  struct timeval help_time;

  spf_change_phase_sub(global_phase);
  quagga_gettime (QUAGGA_CLK_MONOTONIC,&help_time);
  zlog_debug("in func ospf_spf_help_timer,end time at %ld.%ld",help_time.tv_sec,help_time.tv_usec);
  return 0;
}


DEFUN(add_phase,
      add_phase_cmd,
      "add_phase",
      "add phase in cycle\n")
{
  last_phase=global_phase;
  global_phase++;
  if(global_phase==phase_all)
  {
    global_phase=0;
  }

  struct ospf *ospf=ospf_lookup ();
  //struct ospf_lsdb *tmp;
  struct ospf_lsa *lsa,*lsa1,*lsa_dup;
  //struct router_lsa *rl;
  struct route_node *rn,*rn1;
  struct route_table *db;
  struct ospf_area *area;

  struct timeval help_time;
  quagga_gettime (QUAGGA_CLK_MONOTONIC,&help_time);

  zlog_debug("in func add phase,now phase=%d,begin time at %ld.%ld",global_phase,help_time.tv_sec,help_time.tv_usec);
  area=ospf->backbone;
  db=ospf->backbone->lsdb->type[OSPF_ROUTER_LSA].db;
  if(area==NULL || db==NULL)
  {
    return CMD_WARNING;
  }
  //manage database
  for(rn=route_top(db);rn;rn=route_next(rn))
  {
    zlog_debug("rn->id=%x,prefixlen=%d",rn->p.u.prefix4.s_addr,rn->p.prefixlen);
    lsa=(struct ospf_lsa *)rn->info;
    if(lsa!=NULL)
    {
      lsa1=NULL;
      if(lsa->phase_count!=0)
      {
        zlog_debug("this lsa has phase,continue");
        continue;
      }
      //look for corespoding lsa store in vty_test_lsdb
      for(rn1=route_top(vty_test_db->type[OSPF_ROUTER_LSA].db);rn1;rn1=route_next(rn1))
      {
        lsa1=(struct ospf_lsa *)rn1->info;
        if(lsa1!=NULL)
        {
          if(lsa1->data->id.s_addr==lsa->data->id.s_addr)
          {
            break;
          }
        }
      }
      if(lsa1!=NULL)
      {
        //compare with last_phase, not next phase
        if(is_lsa_recover(lsa,lsa1,last_phase)==1)
        {
          zlog_debug("this lsa don't recover, retain in lsdb");
          continue;
        }
        //this lsa has recover, substitute with phase lsa
        lsa_dup=ospf_lsa_dup(lsa1);
        lsa_dup->area=area;
        lsa_dup->lsdb=ospf->backbone->lsdb;
        ospf_lsa_install(ospf,NULL,lsa_dup);
      }

      zlog_debug("install a lsa success");
    }
  }
  manage_ase(last_phase);
  //do predicted linkdown and begin testing for predicted link up
  struct listnode *node, *nnode;
  struct neighbor_info *nbr_info;
  for(ALL_LIST_ELEMENTS(neighbor_info_list_cur->n_list,node,nnode,nbr_info))
  {
    if(nbr_info->phase_info[global_phase]==1 && nbr_info->phase_info[last_phase]==0)
    {
      //predicted link down in 10 seconds
      predicted_linkdown_sub(nbr_info->router_id);
    }
    if(nbr_info->phase_info[global_phase]==0 && nbr_info->phase_info[last_phase]==1)
    {
      //begin testing and do predicted link up in 10 seconds
      begin_testing_sub(nbr_info->router_id,0);
    }
  }

  //change ip route static
  // zlog_debug("in func ospf add phase, begin manage ip route static");
  // struct in_addr peer_addr,peer_router_id;
  // char peer_str[20];
  // char cmd_route[80];
  // peer_addr.s_addr=0;
  // peer_router_id.s_addr=0;
  // struct ospf_interface *oi;
  // struct ospf_neighbor *nbr;
  // struct listnode *node1,*nnode1,*node2,*nnode2;

  // struct se_ase_info *se_ase_info;

  // for(ALL_LIST_ELEMENTS(ospf->oiflist,node,nnode,oi))
  // {
  //   if(oi->type==OSPF_IFTYPE_INTEROA)
  //   {
  //     peer_addr.s_addr=oi->if_oa_peer.s_addr;

  //     for(rn=route_top(oi->nbrs);rn;rn=route_next(rn))
  //     {
  //       if(nbr=(struct ospf_neighbor *)rn->info)
  //       {
  //         peer_router_id.s_addr=nbr->router_id.s_addr;
  //       }
  //     }

  //     sprintf(peer_str,"%s",inet_ntoa(peer_addr));
  //   }
  // }

  // for(ALL_LIST_ELEMENTS(neighbor_info_list_cur->n_list,node,nnode,nbr_info))
  // {
  //   //look for the nbr_info of if_oa peer
  //   if(nbr_info->router_id.s_addr==peer_router_id.s_addr)
  //   {
  //     //if the link predicedlinkup in next phase
  //     if(nbr_info->phase_info[global_phase]==0 && nbr_info->phase_info[last_phase]==1)
  //     {
  //       //add ip route static

  //       for(ALL_LIST_ELEMENTS(se_ase_info_list_cur->se_ase_list,node1,nnode1,se_ase_info))
  //       {
  //         //look for se_ase_info of self, if self is enable, add ip route static
  //         if(se_ase_info->router_id.s_addr==ospf->router_id_static.s_addr && se_ase_info->enable==se_ase_enable)
  //         {
  //           LSDB_LOOP(EXTERNAL_LSDB(ospf),rn,lsa)
  //           {
  //             if(lsa->data->adv_router.s_addr == ospf->router_id_static.s_addr)
  //             {
  //               sprintf(cmd_route,"ip route add %s/16 via %s",inet_ntoa(lsa->data->id),peer_str);
  //               zlog_debug("in func add_phase,cmd_route=%s",cmd_route);
  //               system(cmd_route);
  //             }
  //           }
  //         }
  //       }
  //     }
  //     //if the link predictedlinkdown in next phase
  //     else if (nbr_info->phase_info[global_phase]==1 && nbr_info->phase_info[last_phase]==0)
  //     {
  //       //del ip route static
  //       for(ALL_LIST_ELEMENTS(se_ase_info_list_cur->se_ase_list,node1,nnode1,se_ase_info))
  //       {
  //         //look for se_ase_info of self
  //         if(se_ase_info->router_id.s_addr==ospf->router_id_static.s_addr && se_ase_info->enable==se_ase_enable)
  //         {
  //           LSDB_LOOP(EXTERNAL_LSDB(ospf),rn,lsa)
  //           {
  //             if(lsa->data->adv_router.s_addr == ospf->router_id_static.s_addr)
  //             {
  //               sprintf(cmd_route,"ip route del %s/16",inet_ntoa(lsa->data->id));
  //               zlog_debug("in func add_phase,cmd_route=%s",cmd_route);
  //               system(cmd_route);
  //             }
  //           }
  //         }
  //       }
  //     }      
  //   }
  // }
  //do spf calculation
  ospf->t_spf_help=thread_add_timer(master, ospf_spf_help_timer, ospf, 11);
  return CMD_SUCCESS;
}

DEFUN(begin_running,
      begin_running_cmd,
      "begin_running",
      "begin_running\n")
{
  struct ospf *ospf=ospf_lookup ();
    //do predicted linkdown and begin testing for predicted link up
  struct listnode *node, *nnode;
  struct neighbor_info *nbr_info;
  for(ALL_LIST_ELEMENTS(neighbor_info_list_cur->n_list,node,nnode,nbr_info))
  {
    //down the link in first phase
    if(nbr_info->phase_info[0]==1)
    {
      //predicted link down in 10 seconds
      predicted_linkdown_sub(nbr_info->router_id);
    }
  }
  ospf->t_spf_help=thread_add_timer(master, ospf_spf_help_timer, ospf, 10);
  return CMD_SUCCESS;
}

DEFUN(if_inter_oa,
      if_inter_oa_cmd,
      "if_inter_oa A.B.C.D A.B.C.D ",
      "if_inter_oa in_addr peer_addr \n")
{

  zlog_debug("in func if_inter_oa,argv[0]=%s",argv[0]);
  struct interface *ifp = vty->index;
  struct ospf_interface *oi;
  struct listnode *cnode;
  struct connected *co;
  struct ospf *ospf=ospf_lookup();
  struct in_addr addr_help;
  //here is network byte sequence
  inet_aton(argv[0],&addr_help);
  

  //copy from ospf_network_run_interface, here is not only one co?


  for(ALL_LIST_ELEMENTS_RO (ifp->connected, cnode, co))
  {
    if(addr_help.s_addr==co->address->u.prefix4.s_addr)
    {
      oi = ospf_if_new (ospf, ifp, co->address);
      inet_aton(argv[1],&oi->if_oa_peer);
      oi->type = OSPF_IFTYPE_INTEROA;
      oi=ospf_if_new(ospf,ifp,co->address);
      oi->connected = co;
      oi->params = ospf_lookup_if_params (ifp, oi->address->u.prefix4);
      oi->area = ospf->backbone;
      zlog_debug("in func if_inter_oa 1,co->address=%x/%d,co->des=%x/%d",co->address->u.prefix4.s_addr,co->address->prefixlen,co->destination->u.prefix4.s_addr,co->destination->prefixlen);
      ospf_nbr_add_self (oi);
      zlog_debug("in func if_inter_oa 2");
      if ((ospf->router_id.s_addr != 0) && if_is_operative (ifp)) 
        ospf_if_up (oi);
    }
  }
  return CMD_SUCCESS;
}

DEFUN(if_se,
      if_se_cmd,
      "if_se",
      "if_se\n")
{
  struct interface *ifp = vty->index;
  struct ospf_interface *oi;
  struct listnode *cnode;
  struct connected *co;
  struct connected *co_dup;
  struct ospf *ospf=ospf_lookup();
  for(ALL_LIST_ELEMENTS_RO (ifp->connected, cnode, co))
  {
    if(co->address->family==AF_INET)
    {
      oi = ospf_if_new (ospf, ifp, co->address);
      oi->type = OSPF_IFTYPE_SE;
      oi=ospf_if_new(ospf,ifp,co->address);
      oi->connected = co;
      oi->params = ospf_lookup_if_params (ifp, oi->address->u.prefix4);
      oi->area = ospf->backbone;
      ospf_nbr_add_self (oi);
      ospf_area_add_if (oi->area, oi);
    
      if ((ospf->router_id.s_addr != 0) && if_is_operative (ifp)) 
        ospf_if_up (oi);
    }
  }
  return CMD_SUCCESS;
}

DEFUN(print_co_info,
      print_co_info_cmd,
      "print_co_info",
      "print connected info for a interface\n")
{
  struct interface *ifp = vty->index;
  struct ospf_interface *oi;
  struct listnode *node,*nnode;
  struct connected *co;
  struct ospf *ospf=ospf_lookup();
  zlog_debug("in func print_co_info");  
  for(ALL_LIST_ELEMENTS_RO (ifp->connected,node, co))
  {
    if (CHECK_FLAG(co->flags,ZEBRA_IFA_SECONDARY))
    {
      zlog_debug("chenck  flag fail ,this connected can't be printed");
      continue;
    }
    if(co->address->family !=AF_INET)
    {
      zlog_debug("co->address->family == %d,continue",co->address->family);
    }
    else{
      zlog_debug("co->address->family == %d, need print",co->address->family);
      zlog_debug("addr=%x,des=%x,ifp->ifindex=%x,",co->address->u.prefix4.s_addr,co->destination->u.prefix4.s_addr,co->ifp->ifindex);
    }
  }
  zlog_debug("end in func print_co_info");
  return CMD_SUCCESS;
}

DEFUN(print_exinfo,
      print_exinfo_cmd,
      "print_exinfo",
      "print_exinfo\n")
{
  struct route_table *rt;
  struct route_node *rn;
  struct external_info *ei;
  rt=om->external_info[ZEBRA_ROUTE_STATIC];
  zlog_debug("in func print_exinfo");
  for(rn=route_top(rt);rn;rn=route_next(rn))
  {
    if(rn->info!=NULL)
    {
      ei = rn->info;
      zlog_debug("ei->p=%x,len=%d,ifindex=%d,nexthop=%x,tag=%d,type=%d",ei->p.prefix.s_addr,ei->p.prefixlen,ei->ifindex,ei->nexthop.s_addr,ei->tag,ei->type);
    }
  }
  rt=om->external_info[ZEBRA_ROUTE_CONNECT];
  for(rn=route_top(rt);rn;rn=route_next(rn))
  {
    if(rn->info!=NULL)
    {
      ei = rn->info;
      zlog_debug("ei->p=%x,len=%d,ifindex=%d,nexthop=%x,tag=%d,type=%d",ei->p.prefix.s_addr,ei->p.prefixlen,ei->ifindex,ei->nexthop.s_addr,ei->tag,ei->type);
    }
  }
  zlog_debug("se_prefix=%x/%d",se_prefix->u.prefix4.s_addr,se_prefix->prefixlen);
  return CMD_SUCCESS;
}

//se_info is for add_y, record orbit's phase, and which lsa needs modify when y change
struct se_info_list *se_info_list_cur;

static struct se_info *se_info_new()
{
  struct se_info *se_info=calloc(1,sizeof(struct se_info));
  return se_info;
}
static void se_info_free(void *se_info)
{
  free((struct se_info *)se_info);
}
struct se_info_list *se_info_list_new()
{
  struct se_info_list *se_info_list=calloc(1,sizeof(struct se_info_list));
  se_info_list->se_list=list_new();
  se_info_list->se_list->del=se_info_free;
  return se_info_list;
}
void se_info_list_free(struct se_info_list *se_info_list)
{
  if(se_info_list->se_list!=NULL)
  {
    list_delete(se_info_list->se_list);
  }
  free(se_info_list);
}

DEFUN(input_se_info,
      input_se_info_cmd,
      "input_se_info FILENAME",
      "input_se_info\n")
{
  DATA_INFO_STR data_info_str;
  fileToMatrix_str(argv[0],&data_info_str);
  zlog_debug("in func input_se_info");

  se_info_list_cur->x_add=0;
  se_info_list_cur->x_max=atoi(data_info_str.matrix[0][0]);
  se_info_list_cur->y_max=atoi(data_info_str.matrix[0][1]);
  se_info_list_cur->k_max=atoi(data_info_str.matrix[0][2]);
  se_info_list_cur->se_info_count=atoi(data_info_str.matrix[0][3]);

  struct se_info *se_info;
  for(int i=1;i<1+se_info_list_cur->se_info_count;++i)
  {
    se_info=se_info_new();

    se_info->x=atoi(data_info_str.matrix[i][0]);
    se_info->x0=se_info->x;
    se_info->k=atoi(data_info_str.matrix[i][1]);
    
    listnode_add(se_info_list_cur->se_list,se_info);
  }

  return CMD_SUCCESS;
}

DEFUN(print_se_info,
      print_se_info_cmd,
      "print_se_info",
      "print_se_info\n")
{
  zlog_debug("in func print_se_info");
  zlog_debug("x_max=%d,y_max=%d,k_max=%d,se_info_count=%d,x_add=%d",se_info_list_cur->x_max,se_info_list_cur->y_max,se_info_list_cur->k_max,se_info_list_cur->se_info_count,se_info_list_cur->x_add);
  
  struct listnode *node,*nnode;
  struct se_info *se_info;

  for(ALL_LIST_ELEMENTS(se_info_list_cur->se_list,node,nnode,se_info))
  {
    zlog_debug("se_info->x=%d,k=%d,x0=%d",se_info->x,se_info->k,se_info->x0);
  }
  
  return CMD_SUCCESS;
}

static char *get_ip_i_rl(struct ospf_lsa *lsa,int i)
{
  zlog_debug("in func get_ip_i_rl");

  assert(lsa->data->type==OSPF_ROUTER_LSA);
  struct router_lsa *rl=(struct router_lsa *)lsa->data;
  char *ret;
  for(int k=0;k<rl->links;++k)
  {
    if(rl->link[k].type==LSA_LINK_TYPE_SE)
    {
      ret=(char *)&rl->link[k].link_id.s_addr;
      zlog_debug("ip_%d=%d",i,ret[i]);
      zlog_debug("ip_0,1,2,3=%d,%d,%d,%d",ret[0],ret[1],ret[2],ret[3]);
      return &ret[i];
    }
  }
  return NULL;
}

struct se_ase_info_list *se_ase_info_list_cur;

static struct se_ase_info *se_ase_info_new()
{
  struct se_ase_info *p=calloc(1,sizeof(struct se_ase_info));
  p->ase_list=list_new();
  p->ase_list->del=NULL;
  p->enable=se_ase_enable;
  return p;
}
static void se_ase_info_free(void *p)
{
  
  list_delete(((struct se_ase_info *)p)->ase_list);
  free((struct se_ase_info *)p);
}
struct se_ase_info_list *se_ase_info_list_new()
{
  struct se_ase_info_list *p=calloc(1,sizeof(struct se_ase_info_list));
  p->se_ase_list=list_new();
  p->se_ase_list->del=se_ase_info_free;
  return p;
}

void  se_ase_info_list_free(struct se_ase_info_list *p)
{
  if(p->se_ase_list!=NULL)
  {
    list_delete(p->se_ase_list);
  }
  free(p);
}

static void gen_se_ase(struct se_ase_info *p)
{
  struct ospf_lsa *se_ase;
  int i,j;
  struct stream *s=NULL;
  struct lsa_header *lsah;
  u_int32_t s_addr_h;
  struct ospf *ospf=ospf_lookup();
  //struct in_addr mask;
  //int masklen=16;
  //masklen2ip(masklen,&mask);
  zlog_debug("in func gen_se_ase");

  struct as_external_lsa *ase;
  for(i=0;i<p->x_count;++i)
  {
    se_ase=ospf_lsa_new();
    s=stream_new(OSPF_MAX_LSA_SIZE);
    lsah=(struct lsa_header *)STREAM_DATA(s);
    lsah->ls_age=htons (OSPF_LSA_INITIAL_AGE);
    lsah->options=2;
    lsah->type=5;

    s_addr_h=(0xa<<24)+(p->x_list[i]<<16);
    lsah->id.s_addr=htonl(s_addr_h);
    lsah->adv_router.s_addr=p->router_id.s_addr;

    lsah->ls_seqnum=htonl(OSPF_INITIAL_SEQUENCE_NUMBER);
    lsah->length=36;

    stream_forward_endp (s, OSPF_LSA_HEADER_SIZE);

    //mask stream put will change to net seq
    stream_putl(s,0xffff0000);
    //tos
    stream_putc(s,(char)0);
    //cost
    stream_putc(s,(char)0);
    stream_putc(s,(char)0);
    stream_putc(s,(char)20);
    //forward_addr
    stream_putl(s,0);
    //route_tag
    stream_putl(s,0);
    
    se_ase->data=ospf_lsa_data_new(36);
    memcpy(se_ase->data,STREAM_DATA (s),36);
    ospf_lsa_is_self_originated(ospf,se_ase);

    zlog_debug("before checksum calc");
    //lsah->checksum=ospf_lsa_checksum(lsah);
    lsah->checksum=0;
    zlog_debug("after checksum calc");

    se_ase->lock=1;
    se_ase->lsdb=vty_test_db;

    se_ase->links_count=1;
    se_ase->phase_count=p->phase_count;
    se_ase->phase_matrix=calloc(1,sizeof(int *));
    se_ase->phase_matrix[0]=calloc(p->phase_count,sizeof(int));
    for(j=0;j<p->phase_count;++j)
    {
      se_ase->phase_matrix[0][j]=p->phase_vector[j];
    }

    ospf_lsdb_add(vty_test_db,se_ase);

    stream_free(s);
    s=NULL;
    listnode_add(p->ase_list,se_ase);

    ase=(struct as_external_lsa *)se_ase->data;
    zlog_debug("ase->id=%x,adv=%x,mask=%x",ase->header.id.s_addr,ase->header.adv_router.s_addr,ase->mask.s_addr);
  }

}

int predictable_ase_cnt;

void static_inter_star_operation(int add, int predictable)
{
  struct ospf *ospf=ospf_lookup();

  char peer_str[20];
  zlog_debug("in func static_inter_star_operation,add=%d,predictable=%d",add,predictable);

  struct ospf_interface *oi;
  struct in_addr peer_addr;
  struct listnode *node,*nnode,*node1,*nnode1;
  peer_addr.s_addr=0;

  for(ALL_LIST_ELEMENTS(ospf->oiflist,node,nnode,oi))
  {
    if(oi->type==OSPF_IFTYPE_INTEROA)
    {
      peer_addr.s_addr=oi->if_oa_peer.s_addr;
      sprintf(peer_str,"%s",inet_ntoa(peer_addr));
    }
  }
  char cmd_route[50];
  struct ase_info *p;
  struct ospf_lsa *lsa;
  for(ALL_LIST_ELEMENTS(ase_info_list_cur->ase_list,node,nnode,p))
  {
    if(p->adv_router.s_addr==ospf->router_id_static.s_addr)
    {
      for(ALL_LIST_ELEMENTS(p->ase_lsa,node1,nnode1,lsa))
      {
        if(add)
        {
          sprintf(cmd_route,"ip route add %s/20 via %s",inet_ntoa(lsa->data->id),peer_str);
        }
        else
        {
          sprintf(cmd_route,"ip route del %s/20",inet_ntoa(lsa->data->id));
        }
        zlog_debug("in func static_inter_star_operation,cmd_route=%s",cmd_route);
        system(cmd_route);
        if(predictable)
        {
          predictable_ase_cnt++;
          zlog_debug("in func static_inter_star_operation, predictable_ase_cnt=%d",predictable_ase_cnt); 
        } 
      }      
      break;
    }
  }
  zlog_debug("after static_inter_star_operation, predictable_ase_cnt=%d",predictable_ase_cnt);  
}

void remove_se_ase(struct in_addr router_id,int is_self, int predictable)
{
  struct ospf *ospf=ospf_lookup();
  struct route_node *rn;
  struct route_table *rt;
  struct ospf_lsa *lsa;
  struct as_external_lsa *ase;
  struct prefix p;
  rt=ospf->lsdb->type[OSPF_AS_EXTERNAL_LSA].db;

  zlog_debug("in func remove_se_ase,router_id=%x,is_self=%d,predictable=%d",router_id.s_addr,is_self,predictable);

  struct listnode *node,*nnode;
  struct se_ase_info *se_ase_info;
  char change_flag=0;
  for(ALL_LIST_ELEMENTS(se_ase_info_list_cur->se_ase_list,node,nnode,se_ase_info))
  {
    zlog_debug("se_ase_info->router-id=%x,enable=%d",se_ase_info->router_id.s_addr,se_ase_info->enable);
    if(se_ase_info->router_id.s_addr == router_id.s_addr && se_ase_info->enable == se_ase_enable)
    {
      se_ase_info->enable = se_ase_notenable;
      change_flag=1;
      break;
    }
  }
  if (change_flag==0)
  {
    return;
  }
  char cmd_route[50];
  for(rn=route_top(rt);rn;rn=route_next(rn))
  {
    if(rn->info!=NULL)
    {
      lsa=(struct ospf_lsa *)rn->info;
      ase=(struct as_external_lsa *)lsa->data;

      p.u.prefix4.s_addr=lsa->data->id.s_addr;
      p.prefixlen=ip_masklen(ase->mask);

      if(lsa->data->adv_router.s_addr==router_id.s_addr && prefix_match(se_prefix,&p))
      {
        //modify to maxage
        lsa->data->ls_age=htons (OSPF_LSA_MAXAGE);
        //timer on maxage timer
        ospf_lsa_maxage (ospf, lsa);
        if(is_self)
        {
          sprintf(cmd_route,"ip route del %s/16",inet_ntoa(lsa->data->id));
          zlog_debug("in func remove_se_ase,cmd_route=%s",cmd_route);
          system(cmd_route);
          if(predictable)
          {
            predictable_ase_cnt++;
          }
        }
      }
    }
  }
  zlog_debug("after remove_se_ase,predictable_ase_cnt=%d",predictable_ase_cnt);
  ospf_spf_calculate_schedule(ospf);
}
void load_se_ase(struct in_addr router_id,int is_self, int predictable)
{
  struct ospf *ospf=ospf_lookup();

  struct ospf_lsa *lsa,*lsa1;
  struct se_ase_info *se_ase_info;
  struct listnode *node,*nnode,*node1,*nnode1;
  char cmd_route[50];
  char peer_str[20];
  int is_change=0;
  zlog_debug("in func load_se_ase, router_id=%x,is_self=%d,predictable=%d",router_id.s_addr,is_self,predictable);

  struct ospf_interface *oi;
  struct in_addr peer_addr;
  peer_addr.s_addr=0;

  for(ALL_LIST_ELEMENTS(ospf->oiflist,node,nnode,oi))
  {
    if(oi->type==OSPF_IFTYPE_INTEROA)
    {
      peer_addr.s_addr=oi->if_oa_peer.s_addr;
      sprintf(peer_str,"%s",inet_ntoa(peer_addr));
    }
  }
  
  for(ALL_LIST_ELEMENTS(se_ase_info_list_cur->se_ase_list,node,nnode,se_ase_info))
  {
    if(se_ase_info->router_id.s_addr==router_id.s_addr && se_ase_info->enable== se_ase_notenable)
    {
      is_change=1;
      se_ase_info->enable=se_ase_enable;
      for(ALL_LIST_ELEMENTS(se_ase_info->ase_list,node1,nnode1,lsa))
      {
        lsa->data->ls_age=0;
        lsa1=ospf_lsa_dup(lsa);
        lsa1->lsdb=ospf->lsdb;
        lsa1->area=NULL;
        ospf_lsa_install(ospf,NULL,lsa1);
        if(is_self)
        {
          sprintf(cmd_route,"ip route add %s/16 via %s",inet_ntoa(lsa->data->id),peer_str);
          zlog_debug("in func load_se_ase,cmd_route=%s",cmd_route);
          system(cmd_route); 
          if(predictable)
          {
            predictable_ase_cnt++;
          }
        }
      }
      
      break;
    }
  }

  zlog_debug("after load_se_ase,predictable_ase_cnt=%d",predictable_ase_cnt);

  if(is_change==1){
    ospf_spf_calculate_schedule(ospf);
  }
}




DEFUN(test_remove_se_ase,
      test_remove_se_ase_cmd,
      "test_remove_se_ase A.B.C.D <0-1>",
      "test_remove_se_ase A.B.C.D\n")
{
  struct in_addr router_id;
  inet_aton(argv[0],&router_id);
  remove_se_ase(router_id,1,atoi(argv[1]));

  return CMD_SUCCESS;
}

DEFUN(test_load_se_ase,
      test_load_se_ase_cmd,
      "test_load_se_ase A.B.C.D <0-1>",
      "test_load_se_ase A.B.C.D\n")
{
  struct in_addr router_id;
  inet_aton(argv[0],&router_id);
  load_se_ase(router_id,1,atoi(argv[1]));
  return CMD_SUCCESS;
}

DEFUN(input_se_ase_info,
      input_se_ase_info_cmd,
      "input_se_ase_info FILENAME",
      "input_se_ase_info FILENAME\n")
{
  DATA_INFO_STR data_info_str;
  fileToMatrix_str(argv[0],&data_info_str);
  zlog_debug("in func input_se_ase_info");

  struct ospf *ospf=ospf_lookup();

  se_ase_info_list_cur->router_count=atoi(data_info_str.matrix[0][0]);

  struct se_ase_info *p;
  struct listnode *node,*nnode,*node1,*nnode1;
  int i,j;

  struct ospf_interface *oi;
  struct in_addr peer_addr;
  peer_addr.s_addr=0;
  char cmd_route[50];
  char peer_str[20];
  for(ALL_LIST_ELEMENTS(ospf->oiflist,node,nnode,oi))
  {
    if(oi->type==OSPF_IFTYPE_INTEROA)
    {
      peer_addr.s_addr=oi->if_oa_peer.s_addr;
      sprintf(peer_str,"%s",inet_ntoa(peer_addr));
    }
  }

  for(i=1;i<data_info_str.row_total;i=i+2)
  {
    p=se_ase_info_new();
    inet_aton(data_info_str.matrix[i][0],&p->router_id);
    p->enable=se_ase_enable;
    p->x_count=atoi(data_info_str.matrix[i][1]);
    p->x_list=calloc(p->x_count,sizeof(int));
    for(j=2;j<2+p->x_count;++j)
    {
      p->x_list[j-2]=atoi(data_info_str.matrix[i][j]);
    }

    p->phase_count=atoi(data_info_str.matrix[i+1][0]);
    p->phase_vector=calloc(p->phase_count,sizeof(int));
    for(j=1;j<1+p->phase_count;++j)
    {
      p->phase_vector[j-1]=atoi(data_info_str.matrix[i+1][j]);
    }
    listnode_add(se_ase_info_list_cur->se_ase_list,p);

  }
  //gen lsa and install in vty_test_db 
  for(ALL_LIST_ELEMENTS(se_ase_info_list_cur->se_ase_list,node,nnode,p))
  {
    gen_se_ase(p);
  }
  //copy lsa to running lsdb
  struct ospf_lsa *lsa,*lsa1;
  for(ALL_LIST_ELEMENTS(se_ase_info_list_cur->se_ase_list,node,nnode,p))
  {
    for(ALL_LIST_ELEMENTS(p->ase_list,node1,nnode1,lsa))
    {
      lsa1=ospf_lsa_dup(lsa);
      lsa1->lsdb=ospf->lsdb;
      lsa1->area=NULL;
      ospf_lsa_install(ospf,NULL,lsa1);
      if(p->router_id.s_addr==ospf->router_id_static.s_addr)
      {
        sprintf(cmd_route,"ip route add %s/16 via %s",inet_ntoa(lsa->data->id),peer_str);
        zlog_debug("in func input_se_ase_info,p->router_id=%x,cmd_route=%s",p->router_id.s_addr,cmd_route);
        system(cmd_route);
      }
    }
  }
  zlog_debug("after_input_se_ase_info, predictable_ase_cnt=%d",predictable_ase_cnt);
  ospf_spf_calculate_schedule(ospf);
  return CMD_SUCCESS;
}

DEFUN(print_se_ase,
      print_se_ase_cmd,
      "print_se_ase",
      "print_se_ase\n")
{
  zlog_debug("in func print_se_ase");
  struct listnode *node,*nnode;
  struct listnode *node1,*nnode1;
  struct se_ase_info *p;
  struct as_external_lsa *ase;
  for(ALL_LIST_ELEMENTS(se_ase_info_list_cur->se_ase_list,node,nnode,p))
  {
    zlog_debug("se_ase->router-id=%x,x_count=%d,enable=%d,phase=%d",p->router_id.s_addr,p->x_count,p->enable,p->phase_count);
    zlog_debug("x info");
    for(int j=0;j<p->x_count;++j)
    {
      zlog_debug("%d",p->x_list[j]);
    }
    zlog_debug("phase info");
    for(int j=0;j<p->phase_count;++j)
    {
      zlog_debug("%d",p->phase_vector[j]);
    }
    for(ALL_LIST_ELEMENTS(p->ase_list,node1,nnode1,ase))
    {
      zlog_debug("ase->id=%x,adv=%x,mask=%x",ase->header.id.s_addr,ase->header.adv_router.s_addr,ase->mask.s_addr);
    }
  }
  return CMD_SUCCESS;
}


DEFUN(se_add_y,
      se_add_y_cmd,
      "se_add_y",
      "se_add_y\n")
{

  struct listnode *node,*nnode;
  struct se_info *se_info;
  struct ospf *ospf=ospf_lookup();
  struct route_table *rt=ospf->backbone->lsdb->type[OSPF_ROUTER_LSA].db;
  struct route_table *rt_back=vty_test_db->type[OSPF_ROUTER_LSA].db;

  struct route_node *rn;
  struct ospf_lsa *lsa;
  char *ip1,*ip2;

  for(ALL_LIST_ELEMENTS(se_info_list_cur->se_list,node,nnode,se_info))
  {
    se_info->k = (se_info->k+1) % (se_info_list_cur->k_max);

    //after modify, if k=0, then modify ip2
    if(se_info->k==0)
    {
      zlog_debug("modify x=%d 's y here",se_info->x);
      for(rn=route_top(rt);rn;rn=route_next(rn))
      {
        if(rn->info!=NULL)
        {

          lsa=(struct ospf_lsa *)rn->info;
          ip1=get_ip_i_rl(lsa,1);
          ip2=get_ip_i_rl(lsa,2);

          if(ip1==NULL || ip2==NULL)
          {
            return CMD_WARNING;
          }

          zlog_debug("lsa->router-id=%x",lsa->data->adv_router.s_addr);

          zlog_debug("before add, lsa->id1=%d,id2=%d",*ip1,*ip2);
          if(*ip1==(char)se_info->x)
          {
            //*ip2= ((*ip2)+1) % (se_info_list_cur->y_max) ;
            *ip2-=1;
            if(*ip2<0)
            {
              *ip2+=se_info_list_cur->y_max;
            }
            zlog_debug("after add, lsa->id1=%d,id2=%d",*ip1,*ip2);
          }
          else
          {
            zlog_debug("don't add");
          }
          
        }
      }
      //modify vty_tmp_db backup 
      for(rn=route_top(rt_back);rn;rn=route_next(rn))
      {
        if(rn->info!=NULL)
        {

          lsa=(struct ospf_lsa *)rn->info;
          ip1=get_ip_i_rl(lsa,1);
          ip2=get_ip_i_rl(lsa,2);

          if(ip1==NULL || ip2==NULL)
          {
            return CMD_WARNING;
          }
          if(*ip1==(char)se_info->x)
          {
            *ip2-=1;
            if(*ip2<0)
            {
              *ip2+=se_info_list_cur->y_max;
            }
          }          
        }
      }

    }
    zlog_debug("after add, se_info->x=%d,k=%d,x0=%d",se_info->x,se_info->k,se_info->x0);
  }
  ospf_spf_calculate_schedule(ospf);
  return CMD_SUCCESS;
}



DEFUN(se_add_x,
      se_add_x_cmd,
      "se_add_x",
      "se_add_x\n")
{
  struct listnode *node,*nnode,*node1,*nnode1;
  struct se_info *se_info;
  struct ospf *ospf=ospf_lookup();

  struct route_table *rt=ospf->backbone->lsdb->type[OSPF_ROUTER_LSA].db;
  struct route_table *rt_back=vty_test_db->type[OSPF_ROUTER_LSA].db;

  struct route_node *rn;
  struct ospf_lsa *lsa,*lsa1;
  char *ip1;
  char x_before;
  char cmd_route[50];


  zlog_debug("in func se_add_x");

  for(rn=route_top(rt);rn;rn=route_next(rn))
  {
    if(rn->info!=NULL)
    {
      lsa=(struct ospf_lsa *)rn->info;
      lsa->se_x_flag=se_x_not_modify;
    }
  }
  for(rn=route_top(rt_back);rn;rn=route_next(rn))
  {
    if(rn->info!=NULL)
    {
      lsa=(struct ospf_lsa *)rn->info;
      lsa->se_x_flag=se_x_not_modify;
    }
  }

  //modify inner oa route 
  for(ALL_LIST_ELEMENTS(se_info_list_cur->se_list,node,nnode,se_info))
  {
    x_before=(char)se_info->x;
    se_info->x=(se_info->x+1) % (se_info_list_cur->x_max);
    se_info_list_cur->x_add++;
    //modify running lsdb

    for(rn=route_top(rt);rn;rn=route_next(rn))
    {
      if(rn->info!=NULL)
      {

        lsa=(struct ospf_lsa *)rn->info;
        ip1=get_ip_i_rl(lsa,1);
        zlog_debug("lsa->router-id=%x",lsa->data->adv_router.s_addr);
        zlog_debug("before add, lsa->id1=%d,lsa->se_x_flag=%d",*ip1,lsa->se_x_flag);
        if(ip1==NULL )
        {
          return CMD_WARNING;
        }
        if(*ip1==x_before && lsa->se_x_flag==se_x_not_modify)
        {
          *ip1=(x_before+1)%(se_info_list_cur->x_max);
          lsa->se_x_flag=se_x_modify;
          zlog_debug("after add, lsa->id1=%d,lsa->se_x_flag=%d",*ip1,lsa->se_x_flag);
        }
      }
    }
    //modify backup 

    for(rn=route_top(rt_back);rn;rn=route_next(rn))
    {
      if(rn->info!=NULL)
      {

        lsa=(struct ospf_lsa *)rn->info;
        ip1=get_ip_i_rl(lsa,1);

        if(ip1==NULL )
        {
          return CMD_WARNING;
        }
        if(*ip1==x_before && lsa->se_x_flag==se_x_not_modify)
        {
          *ip1=(x_before+1)%(se_info_list_cur->x_max);
          lsa->se_x_flag=se_x_modify;
        }
      }
    }

  }
  zlog_debug("in func se_add_x, after modify inner oa route");
  //modify inter_oa route
  rt=ospf->lsdb->type[OSPF_AS_EXTERNAL_LSA].db;
  rt_back=ospf->lsdb->type[OSPF_AS_EXTERNAL_LSA].db;

  struct prefix lsa_p;
  struct as_external_lsa *ase;

  for(rn=route_top(rt);rn;rn=route_next(rn))
  {
    if(rn->info!=NULL)
    {
      lsa=(struct ospf_lsa *)rn->info;
      if(lsa->data->type==OSPF_AS_EXTERNAL_LSA)
      {
        ase=(struct as_external_lsa *)lsa->data;
        lsa_p.u.prefix4.s_addr=ase->header.id.s_addr;
        lsa_p.prefixlen=ip_masklen(ase->mask);
        if(prefix_match(se_prefix,&lsa_p))
        {
          //delete lsa
          //modify to maxage
          lsa->data->ls_age=htons (OSPF_LSA_MAXAGE);
          //timer on maxage timer
          ospf_lsa_maxage (ospf, lsa);
          if(lsa->data->adv_router.s_addr==ospf->router_id_static.s_addr)
          {
            sprintf(cmd_route,"ip route del %s/16",inet_ntoa(lsa->data->id));
            zlog_debug("in func add_x,lsa->id=%x,cmd_route=%s",lsa->data->adv_router.s_addr,cmd_route);
            system(cmd_route);
            predictable_ase_cnt++;
          }
        }
      }
    }
  }
  zlog_debug("in func se_add_x, after delete running lsdb");
  for(rn=route_top(rt_back);rn;rn=route_next(rn))
  {
    if(rn->info!=NULL)
    {
      lsa=(struct ospf_lsa *)rn->info;
      if(lsa->data->type==OSPF_AS_EXTERNAL_LSA)
      {
        ase=(struct as_external_lsa *)lsa->data;
        lsa_p.u.prefix4.s_addr=ase->header.id.s_addr;
        lsa_p.prefixlen=ip_masklen(ase->mask);
        if(prefix_match(se_prefix,&lsa_p))
        {
          //delete lsa
          //modify to maxage
          lsa->data->ls_age=htons (OSPF_LSA_MAXAGE);
          //timer on maxage timer
          ospf_lsa_maxage (ospf, lsa);
        }
      }
    }
  }
  zlog_debug("in func se_add_x, after delete backup lsdb");
  struct se_ase_info *p;
  struct ospf_interface *oi;
  struct in_addr peer_addr;
  char peer_str[20];
  peer_addr.s_addr=0;

  for(ALL_LIST_ELEMENTS(ospf->oiflist,node,nnode,oi))
  {
    if(oi->type==OSPF_IFTYPE_INTEROA)
    {
      peer_addr.s_addr=oi->if_oa_peer.s_addr;
      sprintf(peer_str,"%s",inet_ntoa(peer_addr));
    }
  }

  for(ALL_LIST_ELEMENTS(se_ase_info_list_cur->se_ase_list,node,nnode,p))
  {
    for(int i=0;i<p->x_count;++i)
    {
      p->x_list[i]=(p->x_list[i]+1)%(se_info_list_cur->x_max);

    }
    list_delete_all_node(p->ase_list);
    gen_se_ase(p);
    zlog_debug("in func se_add_x, after gen_se_ase p->router-id=%x",ntohl(p->router_id.s_addr));
    for(ALL_LIST_ELEMENTS(p->ase_list,node1,nnode1,lsa))
    {
      lsa1=ospf_lsa_dup(lsa);
      lsa1->lsdb=ospf->lsdb;
      lsa1->area=NULL;
      ospf_lsa_install(ospf,NULL,lsa1);
      if(p->router_id.s_addr==ospf->router_id_static.s_addr)
      {
        sprintf(cmd_route,"ip route add %s/16 via %s",inet_ntoa(lsa->data->id),peer_str);
        zlog_debug("in func se_add_x,p->id=%x,cmd_route=%s",p->router_id.s_addr,cmd_route);
        system(cmd_route);
        predictable_ase_cnt++;
      }
    }
    zlog_debug("in func se_add_x, after lsa_dup install");
  }
  zlog_debug("after se_add_x, predictable_ase_cnt=%d",predictable_ase_cnt);
  ospf_spf_calculate_schedule(ospf);
  return CMD_SUCCESS;
}

DEFUN(test_system,
      test_system_cmd,
      "test_system STRING",
      "test_system\n")
{
  char string[50];
  sprintf(string,"echo %s > /home/wyc/test_system.txt",argv[0]);
  
  system(string);
  return CMD_SUCCESS;
}

DEFUN(load_station,
      load_station_cmd,
      "load_station FILENAME",
      "load_station\n")
{
  DATA_INFO_STR data_info_str;
  fileToMatrix_str(argv[0],&data_info_str);

  return CMD_SUCCESS;
}

void
ospf_vty_show_init (void)
{

  /*ospf+ new cmd*/
  install_element (VIEW_NODE,&output_lsdb_cmd);
  install_element (ENABLE_NODE,&output_lsdb_cmd);
  install_element (CONFIG_NODE,&output_lsdb_cmd);
  install_element (VIEW_NODE,&input_lsdb_cmd);
  install_element (ENABLE_NODE,&input_lsdb_cmd);
  install_element (CONFIG_NODE,&input_lsdb_cmd);
  install_element (VIEW_NODE,&change_lsdb_cmd);
  install_element (ENABLE_NODE,&change_lsdb_cmd);
  install_element (CONFIG_NODE,&change_lsdb_cmd);

  install_element (VIEW_NODE,&load_lsdb_cmd);
  install_element (ENABLE_NODE,&load_lsdb_cmd);
  install_element (CONFIG_NODE,&load_lsdb_cmd);  

  install_element (VIEW_NODE,&see_lsdb_cmd);
  install_element (ENABLE_NODE,&see_lsdb_cmd);
  install_element (CONFIG_NODE,&see_lsdb_cmd);  

  install_element (VIEW_NODE,&spf_change_phase_cmd);
  install_element (ENABLE_NODE,&spf_change_phase_cmd);
  install_element (CONFIG_NODE,&spf_change_phase_cmd);
  install_element (VIEW_NODE,&predicted_linkdown_cmd);
  install_element (ENABLE_NODE,&predicted_linkdown_cmd);
  install_element (CONFIG_NODE,&predicted_linkdown_cmd);
  install_element (VIEW_NODE,&predicted_linkup_cmd);
  install_element (ENABLE_NODE,&predicted_linkup_cmd);
  install_element (CONFIG_NODE,&predicted_linkup_cmd);

  install_element (VIEW_NODE,&spf_test_cmd);
  install_element (ENABLE_NODE,&spf_test_cmd);
  install_element (CONFIG_NODE,&spf_test_cmd);

  install_element (VIEW_NODE,&readneighbor_cmd);
  install_element (ENABLE_NODE,&readneighbor_cmd);
  install_element (CONFIG_NODE,&readneighbor_cmd);
  install_element (VIEW_NODE,&print_neighbor_cmd);
  install_element (ENABLE_NODE,&print_neighbor_cmd);
  install_element (CONFIG_NODE,&print_neighbor_cmd);


  install_element (VIEW_NODE,&test_timer_cmd);
  install_element (ENABLE_NODE,&test_timer_cmd);
  install_element (CONFIG_NODE,&test_timer_cmd);

  install_element (VIEW_NODE,&begin_testing_cmd);
  install_element (ENABLE_NODE,&begin_testing_cmd);
  install_element (CONFIG_NODE,&begin_testing_cmd);

  install_element (VIEW_NODE, &print_nbr_rxmt_cmd);
  install_element (ENABLE_NODE, &print_nbr_rxmt_cmd);

  install_element(VIEW_NODE,&print_ase_cmd);
  install_element(ENABLE_NODE,&print_ase_cmd);

  install_element(VIEW_NODE,&print_backbone_cmd);
  install_element(ENABLE_NODE,&print_backbone_cmd);


  install_element(VIEW_NODE,&print_ospf_info_cmd);
  install_element(ENABLE_NODE,&print_ospf_info_cmd);
  install_element(CONFIG_NODE,&print_ospf_info_cmd);

  install_element(VIEW_NODE,&set_phase_all_cmd);
  install_element(ENABLE_NODE,&set_phase_all_cmd);
  install_element(CONFIG_NODE,&set_phase_all_cmd);

  install_element(VIEW_NODE,&add_phase_cmd);
  install_element(ENABLE_NODE,&add_phase_cmd);
  install_element(CONFIG_NODE,&add_phase_cmd);
    
  install_element(VIEW_NODE,&test_is_lsa_recover_cmd);
  install_element(ENABLE_NODE,&test_is_lsa_recover_cmd);
  install_element(CONFIG_NODE,&test_is_lsa_recover_cmd);

  install_element(VIEW_NODE,&print_phase_cmd);
  install_element(ENABLE_NODE,&print_phase_cmd);
  install_element(CONFIG_NODE,&print_phase_cmd);
  
  install_element(VIEW_NODE,&test_system_cmd);
  install_element(ENABLE_NODE,&test_system_cmd);
  install_element(CONFIG_NODE,&test_system_cmd);

  /* phase ase cmd*/
  install_element(VIEW_NODE,&ase_output_cmd);
  install_element(ENABLE_NODE,&ase_output_cmd);
  install_element(CONFIG_NODE,&ase_output_cmd);

  install_element(VIEW_NODE,&ase_input_cmd);
  install_element(ENABLE_NODE,&ase_input_cmd);
  install_element(CONFIG_NODE,&ase_input_cmd);

  install_element(VIEW_NODE,&ase_changelsdb_cmd);
  install_element(ENABLE_NODE,&ase_changelsdb_cmd);
  install_element(CONFIG_NODE,&ase_changelsdb_cmd);

  install_element(VIEW_NODE,&ase_loadlsdb_cmd);
  install_element(ENABLE_NODE,&ase_loadlsdb_cmd);
  install_element(CONFIG_NODE,&ase_loadlsdb_cmd);

  install_element(VIEW_NODE,&print_ase_info_cmd);
  install_element(ENABLE_NODE,&print_ase_info_cmd);
  install_element(CONFIG_NODE,&print_ase_info_cmd);

  install_element(VIEW_NODE,&test_manage_ase_cmd);
  install_element(ENABLE_NODE,&test_manage_ase_cmd);
  install_element(CONFIG_NODE,&test_manage_ase_cmd);

  install_element(VIEW_NODE,&print_exinfo_cmd);
  install_element(ENABLE_NODE,&print_exinfo_cmd);
  install_element(CONFIG_NODE,&print_exinfo_cmd);

  install_element(VIEW_NODE,&se_add_y_cmd);
  install_element(ENABLE_NODE,&se_add_y_cmd);
  install_element(CONFIG_NODE,&se_add_y_cmd);
  install_element(VIEW_NODE,&se_add_x_cmd);
  install_element(ENABLE_NODE,&se_add_x_cmd);
  install_element(CONFIG_NODE,&se_add_x_cmd);

  install_element(VIEW_NODE,&input_se_info_cmd);
  install_element(ENABLE_NODE,&input_se_info_cmd);
  install_element(CONFIG_NODE,&input_se_info_cmd);
  install_element(VIEW_NODE,&print_se_info_cmd);
  install_element(ENABLE_NODE,&print_se_info_cmd);
  install_element(CONFIG_NODE,&print_se_info_cmd);

  install_element(VIEW_NODE,&input_se_ase_info_cmd);
  install_element(ENABLE_NODE,&input_se_ase_info_cmd);
  install_element(CONFIG_NODE,&input_se_ase_info_cmd);
  install_element(VIEW_NODE,&print_se_ase_cmd);
  install_element(ENABLE_NODE,&print_se_ase_cmd);
  install_element(CONFIG_NODE,&print_se_ase_cmd);

  install_element(VIEW_NODE,&test_remove_se_ase_cmd);
  install_element(ENABLE_NODE,&test_remove_se_ase_cmd);
  install_element(CONFIG_NODE,&test_remove_se_ase_cmd);
  install_element(VIEW_NODE,&test_load_se_ase_cmd);
  install_element(ENABLE_NODE,&test_load_se_ase_cmd);
  install_element(CONFIG_NODE,&test_load_se_ase_cmd);

  install_element(VIEW_NODE,&begin_running_cmd);
  install_element(ENABLE_NODE,&begin_running_cmd);
  install_element(CONFIG_NODE,&begin_running_cmd);



  /* "show ip ospf" commands. */
  install_element (VIEW_NODE, &show_ip_ospf_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_cmd);



  /* "show ip ospf database" commands. */
  install_element (VIEW_NODE, &show_ip_ospf_database_type_cmd);
  install_element (VIEW_NODE, &show_ip_ospf_database_type_id_cmd);
  install_element (VIEW_NODE, &show_ip_ospf_database_type_id_adv_router_cmd);
  install_element (VIEW_NODE, &show_ip_ospf_database_type_adv_router_cmd);
  install_element (VIEW_NODE, &show_ip_ospf_database_type_id_self_cmd);
  install_element (VIEW_NODE, &show_ip_ospf_database_type_self_cmd);
  install_element (VIEW_NODE, &show_ip_ospf_database_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_database_type_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_database_type_id_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_database_type_id_adv_router_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_database_type_adv_router_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_database_type_id_self_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_database_type_self_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_database_cmd);

  /* "show ip ospf interface" commands. */
  install_element (VIEW_NODE, &show_ip_ospf_interface_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_interface_cmd);

  /* "show ip ospf neighbor" commands. */
  install_element (VIEW_NODE, &show_ip_ospf_neighbor_int_detail_cmd);
  install_element (VIEW_NODE, &show_ip_ospf_neighbor_int_cmd);
  install_element (VIEW_NODE, &show_ip_ospf_neighbor_id_cmd);
  install_element (VIEW_NODE, &show_ip_ospf_neighbor_detail_all_cmd);
  install_element (VIEW_NODE, &show_ip_ospf_neighbor_detail_cmd);
  install_element (VIEW_NODE, &show_ip_ospf_neighbor_cmd);
  install_element (VIEW_NODE, &show_ip_ospf_neighbor_all_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_neighbor_int_detail_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_neighbor_int_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_neighbor_id_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_neighbor_detail_all_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_neighbor_detail_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_neighbor_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_neighbor_all_cmd);

  /* "show ip ospf route" commands. */
  install_element (VIEW_NODE, &show_ip_ospf_route_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_route_cmd);
  install_element (VIEW_NODE, &show_ip_ospf_border_routers_cmd);
  install_element (ENABLE_NODE, &show_ip_ospf_border_routers_cmd);
}


/* ospfd's interface node. */
static struct cmd_node interface_node =
{
  INTERFACE_NODE,
  "%s(config-if)# ",
  1
};

/* Initialization of OSPF interface. */
static void
ospf_vty_if_init (void)
{
  /* Install interface node. */
  install_node (&interface_node, config_write_interface);

  install_element (CONFIG_NODE, &interface_cmd);
  install_element (CONFIG_NODE, &no_interface_cmd);
  install_default (INTERFACE_NODE);

  //my interface cmd
  install_element (INTERFACE_NODE, &if_inter_oa_cmd);
  install_element (INTERFACE_NODE, &if_se_cmd);
  install_element (INTERFACE_NODE, &print_co_info_cmd);
  /* "description" commands. */
  install_element (INTERFACE_NODE, &interface_desc_cmd);
  install_element (INTERFACE_NODE, &no_interface_desc_cmd);

  /* "ip ospf authentication" commands. */
  install_element (INTERFACE_NODE, &ip_ospf_authentication_args_addr_cmd);
  install_element (INTERFACE_NODE, &ip_ospf_authentication_args_cmd);
  install_element (INTERFACE_NODE, &ip_ospf_authentication_addr_cmd);
  install_element (INTERFACE_NODE, &ip_ospf_authentication_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_authentication_addr_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_authentication_cmd);
  install_element (INTERFACE_NODE, &ip_ospf_authentication_key_addr_cmd);
  install_element (INTERFACE_NODE, &ip_ospf_authentication_key_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_authentication_key_addr_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_authentication_key_cmd);

  /* "ip ospf message-digest-key" commands. */
  install_element (INTERFACE_NODE, &ip_ospf_message_digest_key_addr_cmd);
  install_element (INTERFACE_NODE, &ip_ospf_message_digest_key_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_message_digest_key_addr_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_message_digest_key_cmd);

  /* "ip ospf cost" commands. */
  install_element (INTERFACE_NODE, &ip_ospf_cost_u32_inet4_cmd);
  install_element (INTERFACE_NODE, &ip_ospf_cost_u32_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_cost_u32_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_cost_u32_inet4_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_cost_inet4_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_cost_cmd);

  /* "ip ospf mtu-ignore" commands. */
  install_element (INTERFACE_NODE, &ip_ospf_mtu_ignore_addr_cmd);
  install_element (INTERFACE_NODE, &ip_ospf_mtu_ignore_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_mtu_ignore_addr_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_mtu_ignore_cmd);

  /* "ip ospf dead-interval" commands. */
  install_element (INTERFACE_NODE, &ip_ospf_dead_interval_addr_cmd);
  install_element (INTERFACE_NODE, &ip_ospf_dead_interval_cmd);
  install_element (INTERFACE_NODE, &ip_ospf_dead_interval_minimal_addr_cmd);
  install_element (INTERFACE_NODE, &ip_ospf_dead_interval_minimal_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_dead_interval_addr_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_dead_interval_cmd);
  
  /* "ip ospf hello-interval" commands. */
  install_element (INTERFACE_NODE, &ip_ospf_hello_interval_addr_cmd);
  install_element (INTERFACE_NODE, &ip_ospf_hello_interval_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_hello_interval_addr_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_hello_interval_cmd);

  /* "ip ospf network" commands. */
  install_element (INTERFACE_NODE, &ip_ospf_network_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_network_cmd);

  /* "ip ospf priority" commands. */
  install_element (INTERFACE_NODE, &ip_ospf_priority_addr_cmd);
  install_element (INTERFACE_NODE, &ip_ospf_priority_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_priority_addr_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_priority_cmd);

  /* "ip ospf retransmit-interval" commands. */
  install_element (INTERFACE_NODE, &ip_ospf_retransmit_interval_addr_cmd);
  install_element (INTERFACE_NODE, &ip_ospf_retransmit_interval_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_retransmit_interval_addr_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_retransmit_interval_cmd);

  /* "ip ospf transmit-delay" commands. */
  install_element (INTERFACE_NODE, &ip_ospf_transmit_delay_addr_cmd);
  install_element (INTERFACE_NODE, &ip_ospf_transmit_delay_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_transmit_delay_addr_cmd);
  install_element (INTERFACE_NODE, &no_ip_ospf_transmit_delay_cmd);

  /* These commands are compatibitliy for previous version. */
  install_element (INTERFACE_NODE, &ospf_authentication_key_cmd);
  install_element (INTERFACE_NODE, &no_ospf_authentication_key_cmd);
  install_element (INTERFACE_NODE, &ospf_message_digest_key_cmd);
  install_element (INTERFACE_NODE, &no_ospf_message_digest_key_cmd);
  install_element (INTERFACE_NODE, &ospf_cost_u32_cmd);
  install_element (INTERFACE_NODE, &ospf_cost_u32_inet4_cmd);
  install_element (INTERFACE_NODE, &no_ospf_cost_cmd);
  install_element (INTERFACE_NODE, &no_ospf_cost_u32_cmd);
  install_element (INTERFACE_NODE, &no_ospf_cost_u32_inet4_cmd);
  install_element (INTERFACE_NODE, &no_ospf_cost_inet4_cmd);
  install_element (INTERFACE_NODE, &ospf_dead_interval_cmd);
  install_element (INTERFACE_NODE, &no_ospf_dead_interval_cmd);
  install_element (INTERFACE_NODE, &ospf_hello_interval_cmd);
  install_element (INTERFACE_NODE, &no_ospf_hello_interval_cmd);
  install_element (INTERFACE_NODE, &ospf_network_cmd);
  install_element (INTERFACE_NODE, &no_ospf_network_cmd);
  install_element (INTERFACE_NODE, &ospf_priority_cmd);
  install_element (INTERFACE_NODE, &no_ospf_priority_cmd);
  install_element (INTERFACE_NODE, &ospf_retransmit_interval_cmd);
  install_element (INTERFACE_NODE, &no_ospf_retransmit_interval_cmd);
  install_element (INTERFACE_NODE, &ospf_transmit_delay_cmd);
  install_element (INTERFACE_NODE, &no_ospf_transmit_delay_cmd);
}

static void
ospf_vty_zebra_init (void)
{
  install_element (OSPF_NODE, &ospf_redistribute_source_type_metric_cmd);
  install_element (OSPF_NODE, &ospf_redistribute_source_metric_type_cmd);
  install_element (OSPF_NODE, &ospf_redistribute_source_type_cmd);
  install_element (OSPF_NODE, &ospf_redistribute_source_metric_cmd);
  install_element (OSPF_NODE, &ospf_redistribute_source_cmd);
  install_element (OSPF_NODE,
		   &ospf_redistribute_source_metric_type_routemap_cmd);
  install_element (OSPF_NODE,
		   &ospf_redistribute_source_type_metric_routemap_cmd);
  install_element (OSPF_NODE, &ospf_redistribute_source_metric_routemap_cmd);
  install_element (OSPF_NODE, &ospf_redistribute_source_type_routemap_cmd);
  install_element (OSPF_NODE, &ospf_redistribute_source_routemap_cmd);
  
  install_element (OSPF_NODE, &no_ospf_redistribute_source_cmd);

  install_element (OSPF_NODE, &ospf_distribute_list_out_cmd);
  install_element (OSPF_NODE, &no_ospf_distribute_list_out_cmd);

  install_element (OSPF_NODE,
		   &ospf_default_information_originate_metric_type_cmd);
  install_element (OSPF_NODE, &ospf_default_information_originate_metric_cmd);
  install_element (OSPF_NODE,
		   &ospf_default_information_originate_type_metric_cmd);
  install_element (OSPF_NODE, &ospf_default_information_originate_type_cmd);
  install_element (OSPF_NODE, &ospf_default_information_originate_cmd);
  install_element (OSPF_NODE,
		   &ospf_default_information_originate_always_metric_type_cmd);
  install_element (OSPF_NODE,
		   &ospf_default_information_originate_always_metric_cmd);
  install_element (OSPF_NODE,
		   &ospf_default_information_originate_always_cmd);
  install_element (OSPF_NODE,
		   &ospf_default_information_originate_always_type_metric_cmd);
  install_element (OSPF_NODE,
		   &ospf_default_information_originate_always_type_cmd);

  install_element (OSPF_NODE,
		   &ospf_default_information_originate_metric_type_routemap_cmd);
  install_element (OSPF_NODE,
		   &ospf_default_information_originate_metric_routemap_cmd);
  install_element (OSPF_NODE,
		   &ospf_default_information_originate_routemap_cmd);
  install_element (OSPF_NODE,
		   &ospf_default_information_originate_type_metric_routemap_cmd);
  install_element (OSPF_NODE,
		   &ospf_default_information_originate_type_routemap_cmd);
  install_element (OSPF_NODE,
		   &ospf_default_information_originate_always_metric_type_routemap_cmd);
  install_element (OSPF_NODE,
		   &ospf_default_information_originate_always_metric_routemap_cmd);
  install_element (OSPF_NODE,
		   &ospf_default_information_originate_always_routemap_cmd);
  install_element (OSPF_NODE,
		   &ospf_default_information_originate_always_type_metric_routemap_cmd);
  install_element (OSPF_NODE,
		   &ospf_default_information_originate_always_type_routemap_cmd);

  install_element (OSPF_NODE, &no_ospf_default_information_originate_cmd);

  install_element (OSPF_NODE, &ospf_default_metric_cmd);
  install_element (OSPF_NODE, &no_ospf_default_metric_cmd);
  install_element (OSPF_NODE, &no_ospf_default_metric_val_cmd);

  install_element (OSPF_NODE, &ospf_distance_cmd);
  install_element (OSPF_NODE, &no_ospf_distance_cmd);
  install_element (OSPF_NODE, &no_ospf_distance_ospf_cmd);
  install_element (OSPF_NODE, &ospf_distance_ospf_intra_cmd);
  install_element (OSPF_NODE, &ospf_distance_ospf_intra_inter_cmd);
  install_element (OSPF_NODE, &ospf_distance_ospf_intra_external_cmd);
  install_element (OSPF_NODE, &ospf_distance_ospf_intra_inter_external_cmd);
  install_element (OSPF_NODE, &ospf_distance_ospf_intra_external_inter_cmd);
  install_element (OSPF_NODE, &ospf_distance_ospf_inter_cmd);
  install_element (OSPF_NODE, &ospf_distance_ospf_inter_intra_cmd);
  install_element (OSPF_NODE, &ospf_distance_ospf_inter_external_cmd);
  install_element (OSPF_NODE, &ospf_distance_ospf_inter_intra_external_cmd);
  install_element (OSPF_NODE, &ospf_distance_ospf_inter_external_intra_cmd);
  install_element (OSPF_NODE, &ospf_distance_ospf_external_cmd);
  install_element (OSPF_NODE, &ospf_distance_ospf_external_intra_cmd);
  install_element (OSPF_NODE, &ospf_distance_ospf_external_inter_cmd);
  install_element (OSPF_NODE, &ospf_distance_ospf_external_intra_inter_cmd);
  install_element (OSPF_NODE, &ospf_distance_ospf_external_inter_intra_cmd);
#if 0
  install_element (OSPF_NODE, &ospf_distance_source_cmd);
  install_element (OSPF_NODE, &no_ospf_distance_source_cmd);
  install_element (OSPF_NODE, &ospf_distance_source_access_list_cmd);
  install_element (OSPF_NODE, &no_ospf_distance_source_access_list_cmd);
#endif /* 0 */
}

static struct cmd_node ospf_node =
{
  OSPF_NODE,
  "%s(config-router)# ",
  1
};


/* Install OSPF related vty commands. */
void
ospf_vty_init (void)
{
  /* Install ospf top node. */
  install_node (&ospf_node, ospf_config_write);

  /* "router ospf" commands. */
  install_element (CONFIG_NODE, &router_ospf_cmd);
  install_element (CONFIG_NODE, &no_router_ospf_cmd);

  install_default (OSPF_NODE);
  
  /* "ospf router-id" commands. */
  install_element (OSPF_NODE, &ospf_router_id_cmd);
  install_element (OSPF_NODE, &no_ospf_router_id_cmd);
  install_element (OSPF_NODE, &router_ospf_id_cmd);
  install_element (OSPF_NODE, &no_router_ospf_id_cmd);

  /* "passive-interface" commands. */
  install_element (OSPF_NODE, &ospf_passive_interface_addr_cmd);
  install_element (OSPF_NODE, &ospf_passive_interface_cmd);
  install_element (OSPF_NODE, &ospf_passive_interface_default_cmd);
  install_element (OSPF_NODE, &no_ospf_passive_interface_addr_cmd);
  install_element (OSPF_NODE, &no_ospf_passive_interface_cmd);
  install_element (OSPF_NODE, &no_ospf_passive_interface_default_cmd);

  /* "ospf abr-type" commands. */
  install_element (OSPF_NODE, &ospf_abr_type_cmd);
  install_element (OSPF_NODE, &no_ospf_abr_type_cmd);

  /* "ospf log-adjacency-changes" commands. */
  install_element (OSPF_NODE, &ospf_log_adjacency_changes_cmd);
  install_element (OSPF_NODE, &ospf_log_adjacency_changes_detail_cmd);
  install_element (OSPF_NODE, &no_ospf_log_adjacency_changes_cmd);
  install_element (OSPF_NODE, &no_ospf_log_adjacency_changes_detail_cmd);

  /* "ospf rfc1583-compatible" commands. */
  install_element (OSPF_NODE, &ospf_rfc1583_flag_cmd);
  install_element (OSPF_NODE, &no_ospf_rfc1583_flag_cmd);
  install_element (OSPF_NODE, &ospf_compatible_rfc1583_cmd);
  install_element (OSPF_NODE, &no_ospf_compatible_rfc1583_cmd);

  /* "network area" commands. */
  install_element (OSPF_NODE, &ospf_network_area_cmd);
  install_element (OSPF_NODE, &no_ospf_network_area_cmd);

  /* "area authentication" commands. */
  install_element (OSPF_NODE, &ospf_area_authentication_message_digest_cmd);
  install_element (OSPF_NODE, &ospf_area_authentication_cmd);
  install_element (OSPF_NODE, &no_ospf_area_authentication_cmd);

  /* "area range" commands.  */
  install_element (OSPF_NODE, &ospf_area_range_cmd);
  install_element (OSPF_NODE, &ospf_area_range_advertise_cmd);
  install_element (OSPF_NODE, &ospf_area_range_cost_cmd);
  install_element (OSPF_NODE, &ospf_area_range_advertise_cost_cmd);
  install_element (OSPF_NODE, &ospf_area_range_not_advertise_cmd);
  install_element (OSPF_NODE, &no_ospf_area_range_cmd);
  install_element (OSPF_NODE, &no_ospf_area_range_advertise_cmd);
  install_element (OSPF_NODE, &no_ospf_area_range_cost_cmd);
  install_element (OSPF_NODE, &no_ospf_area_range_advertise_cost_cmd);
  install_element (OSPF_NODE, &ospf_area_range_substitute_cmd);
  install_element (OSPF_NODE, &no_ospf_area_range_substitute_cmd);

  /* "area virtual-link" commands. */
  install_element (OSPF_NODE, &ospf_area_vlink_cmd);
  install_element (OSPF_NODE, &no_ospf_area_vlink_cmd);

  install_element (OSPF_NODE, &ospf_area_vlink_param1_cmd);
  install_element (OSPF_NODE, &no_ospf_area_vlink_param1_cmd);

  install_element (OSPF_NODE, &ospf_area_vlink_param2_cmd);
  install_element (OSPF_NODE, &no_ospf_area_vlink_param2_cmd);

  install_element (OSPF_NODE, &ospf_area_vlink_param3_cmd);
  install_element (OSPF_NODE, &no_ospf_area_vlink_param3_cmd);

  install_element (OSPF_NODE, &ospf_area_vlink_param4_cmd);
  install_element (OSPF_NODE, &no_ospf_area_vlink_param4_cmd);

  install_element (OSPF_NODE, &ospf_area_vlink_authtype_args_cmd);
  install_element (OSPF_NODE, &ospf_area_vlink_authtype_cmd);
  install_element (OSPF_NODE, &no_ospf_area_vlink_authtype_cmd);

  install_element (OSPF_NODE, &ospf_area_vlink_md5_cmd);
  install_element (OSPF_NODE, &no_ospf_area_vlink_md5_cmd);

  install_element (OSPF_NODE, &ospf_area_vlink_authkey_cmd);
  install_element (OSPF_NODE, &no_ospf_area_vlink_authkey_cmd);

  install_element (OSPF_NODE, &ospf_area_vlink_authtype_args_authkey_cmd);
  install_element (OSPF_NODE, &ospf_area_vlink_authtype_authkey_cmd);
  install_element (OSPF_NODE, &no_ospf_area_vlink_authtype_authkey_cmd);

  install_element (OSPF_NODE, &ospf_area_vlink_authtype_args_md5_cmd);
  install_element (OSPF_NODE, &ospf_area_vlink_authtype_md5_cmd);
  install_element (OSPF_NODE, &no_ospf_area_vlink_authtype_md5_cmd);

  /* "area stub" commands. */
  install_element (OSPF_NODE, &ospf_area_stub_no_summary_cmd);
  install_element (OSPF_NODE, &ospf_area_stub_cmd);
  install_element (OSPF_NODE, &no_ospf_area_stub_no_summary_cmd);
  install_element (OSPF_NODE, &no_ospf_area_stub_cmd);

  /* "area nssa" commands. */
  install_element (OSPF_NODE, &ospf_area_nssa_cmd);
  install_element (OSPF_NODE, &ospf_area_nssa_translate_no_summary_cmd);
  install_element (OSPF_NODE, &ospf_area_nssa_translate_cmd);
  install_element (OSPF_NODE, &ospf_area_nssa_no_summary_cmd);
  install_element (OSPF_NODE, &no_ospf_area_nssa_cmd);
  install_element (OSPF_NODE, &no_ospf_area_nssa_no_summary_cmd);

  install_element (OSPF_NODE, &ospf_area_default_cost_cmd);
  install_element (OSPF_NODE, &no_ospf_area_default_cost_cmd);

  install_element (OSPF_NODE, &ospf_area_shortcut_cmd);
  install_element (OSPF_NODE, &no_ospf_area_shortcut_cmd);

  install_element (OSPF_NODE, &ospf_area_export_list_cmd);
  install_element (OSPF_NODE, &no_ospf_area_export_list_cmd);

  install_element (OSPF_NODE, &ospf_area_filter_list_cmd);
  install_element (OSPF_NODE, &no_ospf_area_filter_list_cmd);

  install_element (OSPF_NODE, &ospf_area_import_list_cmd);
  install_element (OSPF_NODE, &no_ospf_area_import_list_cmd);
  
  /* SPF timer commands */
  install_element (OSPF_NODE, &ospf_timers_spf_cmd);
  install_element (OSPF_NODE, &no_ospf_timers_spf_cmd);
  install_element (OSPF_NODE, &ospf_timers_throttle_spf_cmd);
  install_element (OSPF_NODE, &no_ospf_timers_throttle_spf_cmd);
  
  /* refresh timer commands */
  install_element (OSPF_NODE, &ospf_refresh_timer_cmd);
  install_element (OSPF_NODE, &no_ospf_refresh_timer_val_cmd);
  install_element (OSPF_NODE, &no_ospf_refresh_timer_cmd);
  
  /* max-metric commands */
  install_element (OSPF_NODE, &ospf_max_metric_router_lsa_admin_cmd);
  install_element (OSPF_NODE, &no_ospf_max_metric_router_lsa_admin_cmd);
  install_element (OSPF_NODE, &ospf_max_metric_router_lsa_startup_cmd);
  install_element (OSPF_NODE, &no_ospf_max_metric_router_lsa_startup_cmd);
  install_element (OSPF_NODE, &ospf_max_metric_router_lsa_shutdown_cmd);
  install_element (OSPF_NODE, &no_ospf_max_metric_router_lsa_shutdown_cmd);
  
  /* reference bandwidth commands */
  install_element (OSPF_NODE, &ospf_auto_cost_reference_bandwidth_cmd);
  install_element (OSPF_NODE, &no_ospf_auto_cost_reference_bandwidth_cmd);

  /* "neighbor" commands. */
  install_element (OSPF_NODE, &ospf_neighbor_cmd);
  install_element (OSPF_NODE, &ospf_neighbor_priority_poll_interval_cmd);
  install_element (OSPF_NODE, &ospf_neighbor_priority_cmd);
  install_element (OSPF_NODE, &ospf_neighbor_poll_interval_cmd);
  install_element (OSPF_NODE, &ospf_neighbor_poll_interval_priority_cmd);
  install_element (OSPF_NODE, &no_ospf_neighbor_cmd);
  install_element (OSPF_NODE, &no_ospf_neighbor_priority_cmd);
  install_element (OSPF_NODE, &no_ospf_neighbor_poll_interval_cmd);

  /* Init interface related vty commands. */
  ospf_vty_if_init ();

  /* Init zebra related vty commands. */
  ospf_vty_zebra_init ();
}
