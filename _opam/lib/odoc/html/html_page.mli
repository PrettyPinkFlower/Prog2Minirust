(*
 * Copyright (c) 2016 Thomas Refis <trefis@janestreet.com>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

module Html = Tyxml.Html

(** Supported languages for printing code parts. *)

(** {1 Page creator} *)

val make :
  config:Config.t ->
  url:Odoc_document.Url.Path.t ->
  header:Html_types.flow5_without_header_footer Html.elt list ->
  breadcrumbs:Types.breadcrumbs ->
  sidebar:Html_types.div_content Html.elt list option ->
  toc:Types.toc list ->
  uses_katex:bool ->
  Html_types.div_content Html.elt list ->
  Odoc_document.Renderer.page list ->
  Odoc_document.Renderer.page
(** [make ?theme_uri (body, children)] calls "the page creator" to turn [body]
    into an [[ `Html ] elt]. If [theme_uri] is provided, it will be used to
    locate the theme files, otherwise the HTML output directory is used. *)

val make_src :
  config:Config.t ->
  url:Odoc_document.Url.Path.t ->
  breadcrumbs:Types.breadcrumbs ->
  header:Html_types.flow5_without_header_footer Html.elt list ->
  sidebar:Html_types.div_content Html.elt list option ->
  string ->
  Html_types.div_content Html.elt list ->
  Odoc_document.Renderer.page
(** [make ?theme_uri (body, children)] calls "the page creator" to turn [body]
    into an [[ `Html ] elt]. If [theme_uri] is provided, it will be used to
    locate the theme files, otherwise the HTML output directory is used. *)
