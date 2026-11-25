#!/usr/bin/ruby

#     #title            - frame
#     #!title           - containsverbatim frame
#     #[options] title  - explicit options, must not contain "]"
#     #![options] title
#
#     * text      - itemize
#     *# text     - enumerate (only first item needs #)
#     *& text     - description
#
#     *<2->       - Overlay specification
#     *#<2->, *&<2->
#
#     *name: text - named item
#     *#name: text, *&name: text
#     *<2->name:
#     
#     %%BEGIN-FILTER: bash-command
#       text
#     %%END-FILTER
#
#


class EItem 
  attr_accessor :on_depth, :ty

  def initialize d,ty
    @on_depth=d
    @ty=ty
  end

  def open par
    puts "".ljust(@on_depth - 1) + "\\begin{#{@ty}}#{par}"
  end

  def close
    puts "".ljust(@on_depth - 1) + "\\end{#{@ty}}"
  end
end

$item_stack = []

def depth text
  text.gsub(/\t/,"        ");
  /^( *\*?)/ =~ text
  return $1.length
end

def app_list l,t
  if l=="" or l==nil
    return t
  else
    return l+","+t
  end
end

def process_line text
  if /^[ \t]*%%BEGIN-FILTER:(.*)/ =~ text
    flt=$1
    acc=""
    while gets
      break if /^[ \t]*%%END-FILTER/=~ $_
      #acc=acc+"\n" if acc!=""
      acc=acc+$_;
    end
    acc.chop!
    res=`#{flt} <<HERE
#{acc}
HERE`
    puts res
  elsif /^[ \t]*%/ =~ text
    puts text
  elsif /^[ \t]*$/ =~ text
    puts text
  else
    d = 0
    d = depth text unless text==nil

    while (!$item_stack.empty? && $item_stack.last.on_depth > d)
      $item_stack.last.close
      $item_stack.pop
    end

    if (text != nil)
  
      last_d=0
      last_d=$item_stack.last.on_depth unless $item_stack.empty?
  
      texts=text.strip
  

      #      1     2 3               45                6
      if /^\*(#|&)?(<([0-9\-\.+]+)>)?((|[^ ][^:]*):)? +(.*)/ =~ texts

        itt=$6
        iname=""
        ty="itemize"
        iframes=""

        if $1=="#" then ty="enumerate" end
        if $1=="&" then ty="description" end
        if $3 then iframes="<"+$3+">" end
        if $5 then iname="["+$5+"]" end

        if (d>last_d) 
          s=EItem.new(d,ty)
          $item_stack.push s
          s.open ""
        end

        puts "".ljust(d)+"\\item"+iframes+iname+" "+itt
      elsif /^#(!?) *(\[([^\]]+)\])? *(.*)/ =~texts
        frag=($1 == '!')
        options=$3
        title=$4

        if frag then options=app_list(options, "fragile") end

        if options != nil then options="["+options+"]" end
          
        s=EItem.new(d+1,"frame")
        $item_stack.push s

        s.open "#{options}{#{title}}"
      else
        puts text
      end
    end
  end
end

while gets
  process_line $_
end

process_line nil
