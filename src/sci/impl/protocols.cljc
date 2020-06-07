(ns sci.impl.protocols
  {:no-doc true}
  (:refer-clojure :exclude [defprotocol extend extend-protocol
                            -reset-methods -cache-protocol-fn
                            find-protocol-method find-protocol-impl])
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
  (prn (type ctx) psym)
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
                           `(let [m# (unchecked-get ~fqn-fname "_")]
                              (if-not (nil? m#)
                                (m# ~@sig)
                                (throw
                                 (missing-protocol
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
                                  m# (unchecked-get ~fqn-fname (goog/typeOf x#))]
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
                                       [(keyword fname) {:name fname :arglists (list* sigs) :doc doc}]))
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
                   `(let [~dyn-name (fn
                                      ~@(map (fn [sig]
                                               (expand-dyn fname sig))
                                             sigs))]
                      (defn ~fname
                        ~@(map (fn [sig]
                                 (expand-sig dyn-name
                                             (with-meta (symbol (str slot "$arity$" (count sig)))
                                               {:protocol-prop true})
                                             sig))
                               sigs)))))]
    `(do
       (def ~psym {})
       ~@(map method methods)
       )))

(def extend-protocol {})
(def extend {})
(def -cache-protocol-fn {})
(def defprotocol2 {})
