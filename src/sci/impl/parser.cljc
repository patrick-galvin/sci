(ns sci.impl.parser
  {:no-doc true}
  (:refer-clojure :exclude [read-string])
  (:require
   [edamame.impl.parser :as parser]
   [sci.impl.utils :refer [fully-qualify]]
   [sci.impl.readers :as readers]))

#?(:clj (set! *warn-on-reflection* true))

(def opts
  (parser/normalize-opts
   {:all true
    :read-eval false
    :fn readers/read-fn}))

(defn parse-next
  ([r]
   (parser/parse-next opts r))
  ([ctx r]
   (let [features (:features ctx)
         env (:env ctx)
         env-val @env
         current-ns (:current-ns env-val)
         the-current-ns (get-in env-val [:namespaces current-ns])
         aliases (:aliases the-current-ns)
         auto-resolve (assoc aliases
                             :current current-ns)
         parse-opts (assoc opts
                           :read-cond :allow
                           :features features
                           :auto-resolve auto-resolve
                           :syntax-quote {:resolve-symbol #(fully-qualify env-val %)})
         ret (parser/parse-next parse-opts
                                r)]
     ;; (prn "ret" ret)
     ret)))

;;;; Scratch

(comment
  )
