(******************************************************************************
  Logs
  ******************************************************************************)
open Base
open Core

module Log_entry = struct
  type t = {
    session_id : string;
    time : Time_ns.t;
    important : bool;
    message : string;
  }
end

module Heartbeat = struct
  type t = { session_id : string; time : Time_ns.t; status_message : string }
end

module Logon = struct
  type t = {
    session_id : string;
    time : Time_ns.t;
    user : string;
    credentials : string;
  }
end

let create_log_entry ~session_id ~important message : Log_entry.t =
  { time = Time_ns.now (); session_id; important; message }

let message_to_string ({ important; message; _ } : Log_entry.t) =
  if important then String.uppercase message else message

let is_important t = t.Log_entry.important


type client_info =
 {
  addr: Core_unix.Inet_addr.t;
  port: int;
  user: string;
  credentials: string;
  last_heartbeat_time: Time_ns.t;
 }

let register_heartbeat c hb =
  {
    addr = c.addr;
    port = c.port;
    user = c.user;
    credentials = c.credentials;
    last_heartbeat_time = hb.Heartbeat.time
  }

let register_heartbeat2 c hb =
  {c with last_heartbeat_time = hb.Heartbeat.time}