quickstart
==========

quickstart1
------------

To use Lumache, first install it using pip:

.. code-block:: console

   (.venv) $ pip install lumache


quickstart2
----------------

.. py:function:: enumerate(sequence[, start=0])

   Return an iterator that yields tuples of an index and an item of the
   *sequence*. (And so on.)
aaaa

Creating recipes
----------------

To retrieve a list of random ingredients,
you can use the ``lumache.get_random_ingredients()`` function:

.. autofunction:: lumache.get_random_ingredients

The ``kind`` parameter should be either ``"meat"``, ``"fish"``,
or ``"veggies"``.

Otherwise, :py:func:`lumache.get_random_ingredients`will raise an exception.

.. autoexception:: lumache.InvalidKindError

For example:

>>> import lumache
>>> lumache.get_random_ingredients()
['shells', 'gorgonzola', 'parsley']

*text*

**text**

``text``

thisis\ *one*\ word


* 这是一个项目符号列表.
* 它有两项，
  第二项使用两行.

1. 这是个有序列表.
2. 也有两项.

#. 是个有序列表.
#. 也有两项.

* 这是
* 一个列表

  * 嵌套列表
  * 子项

* 父列表继续

一而
    一二啊觉得弗兰克

术 (term 文本开头行)
   定义术语，必须缩进

   可以有多段组成

原始文本

下一术语（term）
   描述.

| 这些行
| 在源文件里
| 被分隔的一模一样.

这是一段正常文本. 下一段是代码文字::

   它不需要特别处理，仅是
   缩进就可以了.

   它可以有多行.

再是正常的文本段.

+------------------------+------------+----------+----------+
| Header row, column 1   | Header 2   | Header 3 | Header 4 |
| (header rows optional) |            |          |          |
+========================+============+==========+==========+
| body row 1, column 1   | column 2   | column 3 | column 4 |
+------------------------+------------+----------+----------+
| body row 2             | ...        | ...      |          |
+------------------------+------------+----------+----------+

=====  =====  =======
A      B      A and B
=====  =====  =======
False  False  False
True   False  False
False  True   False
True   True   True
=====  =====  =======

使用 `链接文本 <http://example.com/>`_ 可以插入网页链接.

段落里包含 `a link`_.

.. _a link: http://example.com/

=================
This is a heading
=================

# 及上划线表示部分

* 及上划线表示章节

=, 小章节

-, 子章节

^, 子章节的子章节

", 段落

.. math::

   \frac{\mathbb{A} \sum_{t=0}^{N}f(t,k) }{N}

aa :math:`\frac{ \sum_{t=0}^{N}f(t,k) }{N}`