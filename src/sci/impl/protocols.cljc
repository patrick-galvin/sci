(ns sci.impl.protocols
  {:no-doc true}
  (:refer-clojure :exclude [defprotocol extend extend-protocol
                            -reset-methods -cache-protocol-fn
                            find-protocol-method find-protocol-impl
                            missing-protocol])
  (:require [sci.impl.vars :as vars]))

(defn- protocol-prefix [psym]
  (str (-> (str psym)
           (.replace #?(:clj \. :cljs (js/RegExp. "\\." "g")) \$)
           (.replace \/ \$))
       "$"))

(defn defprotocol
  "A protocol is a named set of named methods and their signatures:
  (defprotocol AProtocolName
    ;optional doc string
    \"A doc string for AProtocol abstraction\"
  ;method signatures
    (bar [this a b] \"bar docs\")
    (baz [this a] [this a b] [this a b c] \"baz docs\"))
  No implementations are provided. Docs can be specified for the
  protocol overall and for each method. The above yields a set of
  polymorphic functions and a protocol object. All are
  namespace-qualified by the ns enclosing the definition The resulting
  functions dispatch on the type of their first argument, which is
  required and corresponds to the implicit target object ('this' in
  JavaScript parlance). defprotocol is dynamic, has no special compile-time
  effect, and defines no new types.
  (defprotocol P
    (foo [this])
    (bar-me [this] [this y]))
  (deftype Foo [a b c]
    P
    (foo [this] a)
    (bar-me [this] b)
    (bar-me [this y] (+ c y)))
  (bar-me (Foo. 1 2 3) 42)
  => 45
  (foo
    (let [x 42]
      (reify P
        (foo [this] 17)
        (bar-me [this] x)
        (bar-me [this y] x))))
  => 17"
  [_ _ ctx psym & doc+methods]
  (let [p psym ;; TODO (:name (cljs.analyzer/resolve-var (dissoc &env :locals) psym))
        [opts methods]
        (loop [opts {:protocol-symbol true}
               methods []
               sigs doc+methods]
          (if-not (seq sigs)
            [opts methods]
            (let [[head & tail] sigs]
              (cond
                (string? head)
                (recur (assoc opts :doc head) methods tail)
                (keyword? head)
                (recur (assoc opts head (first tail)) methods (rest tail))
                (seq? head)
                (recur opts (conj methods head) tail)
                :else
                (throw #?(:clj  (Exception.
                                 (str "Invalid protocol, " psym " received unexpected argument"))
                          :cljs (js/Error.
                                 (str "Invalid protocol, " psym " received unexpected argument"))))
                ))))
        psym (vary-meta psym merge opts)
        ns-name (vars/current-ns-name) ;; TODO: (-> &env :ns :name)
        fqn (fn [n] (symbol (str ns-name) (str n)))
        prefix (protocol-prefix p)
        _ (doseq [[mname & arities] methods]
            (when (some #{0} (map count (filter vector? arities)))
              (throw
               #?(:clj (Exception.
                        (str "Invalid protocol, " psym
                             " defines method " mname " with arity 0"))
                  :cljs (js/Error.
                         (str "Invalid protocol, " psym
                              " defines method " mname " with arity 0"))))))
        sig->syms (fn [sig]
                    (if-not (every? symbol? sig)
                      (mapv (fn [arg]
                              (cond
                                (symbol? arg) arg
                                (and (map? arg) (some? (:as arg))) (:as arg)
                                :else (gensym))) sig)
                      sig))
        expand-dyn (fn [fname sig]
                     (let [sig (sig->syms sig)

                           fqn-fname (with-meta (fqn fname) {:cljs.analyzer/no-resolve true})
                           fsig (first sig)

                           ;; construct protocol checks in reverse order
                           ;; check the.protocol/fn["_"] for default impl last
                           check
                           `(let [m# (get ~fqn-fname "_")]
                              (if-not (nil? m#)
                                (m# ~@sig)
                                (throw
                                 (clojure.core/missing-protocol
                                  ~(str psym "." fname) ~fsig))))

                           ;; then check protocol fn in metadata (only when protocol is marked with :extend-via-metadata true)
                           check
                           (if-not (:extend-via-metadata opts)
                             check
                             `(if-let [meta-impl# (-> ~fsig (meta) (get '~fqn-fname))]
                                (meta-impl# ~@sig)
                                ~check))

                           ;; then check protocol on js string,function,array,object (first dynamic check actually executed)
                           check
                           `(let [x# (if (nil? ~fsig) nil ~fsig)
                                  m# (get ~fqn-fname (type x#))]
                              (if-not (nil? m#)
                                (m# ~@sig)
                                ~check))]
                       `(~sig ~check)))
        expand-sig (fn [dyn-name slot sig]
                     (let [sig (sig->syms sig)

                           fsig (first sig)

                           ;; check protocol property on object (first check executed)
                           check
                           `(if (and (not (nil? ~fsig))
                                     ;; Property access needed here.
                                     (not (nil? (. ~fsig ~(with-meta (symbol (str "-" slot)) {:protocol-prop true})))))
                              (. ~fsig ~slot ~@sig)
                              (~dyn-name ~@sig))]
                       `(~sig ~check)))
        psym (-> psym
                 (vary-meta update-in [:jsdoc] conj "@interface")
                 (vary-meta assoc-in [:protocol-info :methods]
                            (into {}
                                  (map
                                   (fn [[fname & sigs]]
                                     (let [doc (as-> (last sigs) doc
                                                 (when (string? doc) doc))
                                           sigs (take-while vector? sigs)]
                                       [(vary-meta fname assoc :doc doc)
                                        (vec sigs)]))
                                   methods)))
                 ;; for compatibility with Clojure
                 (vary-meta assoc-in [:sigs]
                            (into {}
                                  (map
                                   (fn [[fname & sigs]]
                                     (let [doc (as-> (last sigs) doc
                                                 (when (string? doc) doc))
                                           sigs (take-while vector? sigs)]
                                       [(keyword fname) {:name fname
                                                         :arglists (list* sigs) :doc doc}]))
                                   methods))))
        method (fn [[fname & sigs]]
                 (let [doc (as-> (last sigs) doc
                             (when (string? doc) doc))
                       sigs (take-while vector? sigs)
                       amp nil #_::TODO #_(when (some #{'&} (apply concat sigs))
                                            (cljs.analyzer/warning
                                             :protocol-with-variadic-method
                                             &env {:protocol psym :name fname}))
                       _ nil #_(when-some [existing (get (-> &env :ns :defs) fname)]
                                 (when-not (= p (:protocol existing))
                                   (cljs.analyzer/warning
                                    :protocol-with-overwriting-method
                                    {} {:protocol psym :name fname :existing existing})))
                       slot (symbol (str prefix (munge (name fname))))
                       dyn-name (symbol (str slot "$dyn"))
                       fname (vary-meta fname assoc
                                        :protocol p
                                        :doc doc)]
                   `(do
                      (declare ~fname)
                      (let [~dyn-name (fn
                                        ~@(map (fn [sig]
                                                 (expand-dyn fname sig))
                                               sigs))]
                        (defn ~fname
                          ~@(map (fn [sig]
                                   (expand-sig dyn-name
                                               (with-meta (symbol (str slot "$arity$" (count sig)))
                                                 {:protocol-prop true})
                                               sig))
                                 sigs))))))
        bare-psym (with-meta psym nil)]
    `(do
       (def ~bare-psym {})
       ;; workaround for preventing eval of metadata of psym above, since it contains quoted data
       (alter-meta! (var ~bare-psym) (constantly (quote ~(meta psym))))
       ~@(map method methods)
       )))

(defn missing-protocol [a b]
  (ex-info (str "missing protocol " a "." b) {:a a :b b}))


(defn extend
  "Implementations of protocol methods can be provided using the extend construct:
  (extend AType
    AProtocol
     {:foo an-existing-fn
      :bar (fn [a b] ...)
      :baz (fn ([a]...) ([a b] ...)...)}
    BProtocol
      {...}
    ...)

  extend takes a type/class (or interface, see below), and one or more
  protocol + method map pairs. It will extend the polymorphism of the
  protocol's methods to call the supplied methods when an AType is
  provided as the first argument.
  Method maps are maps of the keyword-ized method names to ordinary
  fns. This facilitates easy reuse of existing fns and fn maps, for
  code reuse/mixins without derivation or composition. You can extend
  an interface to a protocol. This is primarily to facilitate interop
  with the host (e.g. Java) but opens the door to incidental multiple
  inheritance of implementation since a class can inherit from more
  than one interface, both of which extend the protocol. It is TBD how
  to specify which impl to use. You can extend a protocol on nil.
  If you are supplying the definitions explicitly (i.e. not reusing
  exsting functions or mixin maps), you may find it more convenient to
  use the extend-type or extend-protocol macros.
  Note that multiple independent extend clauses can exist for the same
  type, not all protocols need be defined in a single extend call.
  See also:
  extends?, satisfies?, extenders"
  {:added "1.2"}
  [atype & proto+mmaps]
  (doseq [[proto mmap] (partition 2 proto+mmaps)]
    #_(when-not (protocol? proto)
      (throw (IllegalArgumentException.
              (str proto " is not a protocol"))))
    #_(when (implements? proto atype)
      (throw (IllegalArgumentException.
              (str atype " already directly implements " (:on-interface proto) " for protocol:"
                   (:var proto)))))
    #_(-reset-methods (alter-var-root (:var proto) assoc-in [:impls atype] mmap))))

(def extend-protocol {})
(def -cache-protocol-fn {})
(def defprotocol2 {})
